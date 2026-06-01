#!/usr/bin/env python3
"""Audit a Java/JML file for anti-cheating violations.

This extends the conservative scanner in check_jml_cheating.py with three
additional categories required by the audit stage:

  * contract_weakening   — already in check_jml_cheating.py; mirrored here so
                           audit can emit a unified findings.json.
  * unproven_lemma       — helper methods declared but not checkable
                           (native, empty body, assume-only body).
The script emits findings as JSON to --findings (default findings.json beside
the input) and prints them as human-readable lines to stderr. Exit code is
non-zero if any error-severity finding is present.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass, asdict
from pathlib import Path
import re
import sys


CONTRACT_KEYWORDS = ("requires", "ensures", "assignable")


@dataclass
class Finding:
    category: str
    severity: str  # "error" or "warning"
    path: str
    line_no: int
    text: str
    detail: str


# Patterns that are always errors regardless of context.
FORBIDDEN_PATTERNS: list[tuple[str, re.Pattern[str], str]] = [
    ("assume_or_admitted", re.compile(r"//@\s*assume\b|/\*@[^*]*\bassume\b"), "JML assume bypasses proof"),
    ("assume_or_admitted", re.compile(r"\bAdmitted\b"), "Admitted proofs bypass checking"),
    ("assume_or_admitted", re.compile(r"\bskipesc\b"), "skipesc suppresses ESC obligations"),
    ("unchecked_axiom", re.compile(r"\baxiom\b"), "Unchecked axioms are not allowed"),
    ("nowarn_or_suppression", re.compile(r"\bnowarn\b"), "nowarn hides unsolved obligations"),
    (
        "nowarn_or_suppression",
        re.compile(r"@SuppressWarnings\s*\(\s*\"openjml\""),
        "openjml suppression hides obligations",
    ),
    ("reflection_or_runtime_exit", re.compile(r"\bClass\.forName\b|\bjava\.lang\.reflect\b"), "Reflection breaks verification"),
    ("reflection_or_runtime_exit", re.compile(r"\bSystem\.exit\s*\("), "System.exit breaks verification"),
]


# Broad-frame patterns. \everything covers all locations, which lets the
# verifier accept arbitrary mutation; \nothing is fine.
BROAD_FRAME_PATTERNS: list[tuple[re.Pattern[str], str]] = [
    (
        re.compile(r"//@[^\n]*\bassignable\s+\\everything\b"),
        "assignable \\everything is an overly broad frame clause",
    ),
    (
        re.compile(r"//@[^\n]*\bmodifies\s+\\everything\b"),
        "modifies \\everything is an overly broad frame clause",
    ),
]


def normalize_contract_line(line: str) -> str:
    s = line
    if "//@" in s:
        s = s.split("//@", 1)[1]
    elif "/*@" in s:
        s = s.split("/*@", 1)[1]
    s = re.sub(r"\*/$", "", s).strip()
    s = re.sub(r"\s+", " ", s)
    return s


def contract_lines(path: Path) -> list[str]:
    out: list[str] = []
    for raw in path.read_text(encoding="utf-8", errors="replace").splitlines():
        normalized = normalize_contract_line(raw)
        lowered = normalized.lower()
        if any(lowered.startswith(k) for k in CONTRACT_KEYWORDS):
            out.append(normalized)
    return out


def baseline_findings(baseline: Path, candidate: Path) -> list[Finding]:
    cand = set(contract_lines(candidate))
    findings: list[Finding] = []
    for line in contract_lines(baseline):
        if line not in cand:
            findings.append(
                Finding(
                    category="contract_weakening",
                    severity="error",
                    path=str(candidate),
                    line_no=0,
                    text=line,
                    detail="baseline contract clause is missing in the verified source",
                )
            )
    return findings


def scan_forbidden(path: Path) -> list[Finding]:
    findings: list[Finding] = []
    text = path.read_text(encoding="utf-8", errors="replace")
    for line_no, line in enumerate(text.splitlines(), start=1):
        for cat, pattern, detail in FORBIDDEN_PATTERNS:
            if pattern.search(line):
                findings.append(
                    Finding(
                        category=cat,
                        severity="error",
                        path=str(path),
                        line_no=line_no,
                        text=line.strip(),
                        detail=detail,
                    )
                )
    return findings


def scan_broad_frame(path: Path) -> list[Finding]:
    findings: list[Finding] = []
    for line_no, line in enumerate(path.read_text(encoding="utf-8", errors="replace").splitlines(), start=1):
        for pattern, detail in BROAD_FRAME_PATTERNS:
            if pattern.search(line):
                findings.append(
                    Finding(
                        category="broad_frame_clause",
                        severity="error",
                        path=str(path),
                        line_no=line_no,
                        text=line.strip(),
                        detail=detail,
                    )
                )
    return findings


METHOD_DECL_RE = re.compile(
    r"^\s*(?:public\s+|private\s+|protected\s+|static\s+|final\s+|/\*@\s*pure\s*@\*/\s*)*"
    r"(?P<modifiers>(?:\w+\s+)*)"
    r"(?P<ret>[\w\[\]<>]+)\s+(?P<name>\w+)\s*\([^)]*\)\s*(?P<tail>[{;].*)?$"
)


def scan_unproven_lemmas(path: Path) -> list[Finding]:
    """Heuristic: flag helper methods that can't be checked."""
    findings: list[Finding] = []
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    n = len(lines)
    for i, line in enumerate(lines):
        # `native` method declaration anywhere in the body.
        if re.search(r"\bnative\s+\w[\w\[\]]*\s+\w+\s*\(", line):
            findings.append(
                Finding(
                    category="unproven_lemma",
                    severity="error",
                    path=str(path),
                    line_no=i + 1,
                    text=line.strip(),
                    detail="native method has no checkable body",
                )
            )
            continue
        # Method declared with a JML pure/spec block but with an empty body.
        if "{" in line and "}" in line and re.search(r"\w+\s*\(.*\)\s*\{\s*\}", line):
            # Look back for a JML ensures/requires/pure annotation nearby.
            window = "\n".join(lines[max(0, i - 6) : i + 1])
            if re.search(r"//@[^\n]*(ensures|pure)|/\*@[^*]*(ensures|pure)", window):
                findings.append(
                    Finding(
                        category="unproven_lemma",
                        severity="error",
                        path=str(path),
                        line_no=i + 1,
                        text=line.strip(),
                        detail="JML-annotated helper has an empty body",
                    )
                )
                continue
        # `//@ assume`-only method bodies — already caught by FORBIDDEN_PATTERNS;
        # leave as-is.
    return findings


def run_audit(verified: Path, baseline: Path | None) -> list[Finding]:
    findings: list[Finding] = []
    findings.extend(scan_forbidden(verified))
    findings.extend(scan_broad_frame(verified))
    findings.extend(scan_unproven_lemmas(verified))
    if baseline:
        findings.extend(baseline_findings(baseline, verified))
    return findings


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Audit a Java/JML file for anti-cheating violations.")
    parser.add_argument("verified", help="Verified Java/JML file to audit.")
    parser.add_argument("--baseline", help="Original contract-stage Java file for contract-weakening comparison.")
    parser.add_argument("--findings", help="Output path for findings.json (default: alongside verified).")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    verified = Path(args.verified).resolve()
    if not verified.exists():
        print(f"verified file not found: {verified}", file=sys.stderr)
        return 2
    baseline = Path(args.baseline).resolve() if args.baseline else None
    if baseline and not baseline.exists():
        print(f"baseline file not found: {baseline}", file=sys.stderr)
        return 2

    findings = run_audit(verified, baseline)

    out_path = Path(args.findings).resolve() if args.findings else verified.with_name("findings.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(
        json.dumps(
            {
                "verified": str(verified),
                "baseline": str(baseline) if baseline else None,
                "findings": [asdict(f) for f in findings],
            },
            indent=2,
            ensure_ascii=False,
        )
        + "\n",
        encoding="utf-8",
    )

    has_error = False
    for f in findings:
        if f.severity == "error":
            has_error = True
        print(
            f"{f.path}:{f.line_no}: {f.severity}: {f.category}: {f.detail}: {f.text}",
            file=sys.stderr,
        )
    return 1 if has_error else 0


if __name__ == "__main__":
    raise SystemExit(main())

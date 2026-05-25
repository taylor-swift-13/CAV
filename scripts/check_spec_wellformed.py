#!/usr/bin/env python3
"""Contract-stage OpenJML well-formedness gate.

Runs ``openjml -esc`` on a Java/JML file and decides whether the SPEC is
well-formed enough to enter the pipeline. This is deliberately NOT a full proof.
Undischarged verification conditions (Postcondition / Invariant / Assert / loop
/ arithmetic-range / index / nullness) are TOLERATED here -- discharging them is
the verify stage's job. What is fatal is anything that means the spec can never
be proven downstream regardless of invariants:

  * JML/Java parse or type errors (``: error:``),
  * ``NOT IMPLEMENTED`` -- a feature OpenJML's SMT backend cannot translate,
  * the unsupported aggregate quantifiers ``\\num_of`` / ``\\sum`` / ``\\product``,
  * a tool abort that never reached the VC stage.

Exit codes:
  0  well-formed (may still carry undischarged VCs; that is fine for contract)
  1  fatal spec problem; the contract stage must fail here
  2  usage / tooling error (e.g. OpenJML not installed)
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import sys


REPO_ROOT = Path(__file__).resolve().parents[1]
OPENJML_RUNNER = REPO_ROOT / "scripts" / "run_openjml_verify.sh"

# Aggregate quantifiers OpenJML's SMT backend cannot translate. See
# experiences/general/CONTRACT.md "Verifier-Supported Postcondition Shapes".
UNSUPPORTED_QUANTIFIER = re.compile(r"\\(num_of|sum|product)\b")
NOT_IMPLEMENTED = re.compile(r"NOT IMPLEMENTED", re.IGNORECASE)
COMPILE_ERROR = re.compile(r":\d+:\s*error:")
TOOL_ABORT = re.compile(r"Exception in thread|^\s+at [\w.$]+\(", re.MULTILINE)
TOLERATED_VC = re.compile(r"\bverify:|verification failure")
NOT_INSTALLED = re.compile(r"OpenJML is not installed|openjml: not found|command not found")


def run_openjml(java_file: Path) -> tuple[int, str]:
    proc = subprocess.run(
        [str(OPENJML_RUNNER), str(java_file)],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        cwd=REPO_ROOT,
    )
    return proc.returncode, proc.stdout


def classify(java_file: Path, exit_code: int, output: str) -> tuple[bool, list[str], list[str]]:
    """Return (well_formed, fatal_reasons, tolerated_notes)."""
    fatal: list[str] = []
    tolerated: list[str] = []

    source = java_file.read_text(encoding="utf-8", errors="replace")
    for m in UNSUPPORTED_QUANTIFIER.finditer(source):
        fatal.append(
            f"unsupported aggregate quantifier `\\{m.group(1)}` in spec "
            "(OpenJML SMT backend cannot translate it; rewrite with a `pure` "
            "recursive helper -- see experiences/general/CONTRACT.md)"
        )

    for line in output.splitlines():
        if NOT_IMPLEMENTED.search(line):
            fatal.append(f"NOT IMPLEMENTED feature: {line.strip()}")
        elif COMPILE_ERROR.search(line):
            fatal.append(f"parse/type error: {line.strip()}")
        elif TOLERATED_VC.search(line):
            tolerated.append(line.strip())

    if not fatal and exit_code != 0:
        if NOT_INSTALLED.search(output):
            # tooling problem, surfaced by the caller as exit 2.
            return False, ["__tooling__: " + output.strip().splitlines()[0]], tolerated
        if not tolerated and TOOL_ABORT.search(output):
            fatal.append(
                "OpenJML aborted before reaching the VC stage "
                "(no verification conditions were produced)"
            )
        elif not tolerated:
            # nonzero exit, nothing recognized: be conservative.
            fatal.append(
                f"OpenJML exited {exit_code} with no recognizable VC output; "
                "spec likely not well-formed"
            )

    well_formed = not fatal
    return well_formed, fatal, tolerated


def render_report(java_file: Path, exit_code: int, well_formed: bool,
                  fatal: list[str], tolerated: list[str]) -> str:
    lines = [
        "# Contract Spec Well-Formedness",
        "",
        f"- File: `{java_file}`",
        f"- OpenJML exit code: `{exit_code}`",
        f"- Verdict: `{'well-formed' if well_formed else 'fatal'}`",
        "",
    ]
    if fatal:
        lines.append("## Fatal (contract must fail)")
        lines.append("")
        lines.extend(f"- {r}" for r in fatal)
        lines.append("")
    if tolerated:
        lines.append("## Tolerated (undischarged VCs -- verify stage handles these)")
        lines.append("")
        lines.extend(f"- {t}" for t in tolerated)
        lines.append("")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("java_file", help="Java/JML file to check.")
    parser.add_argument("--log-dir", help="Directory to write classification + raw OpenJML logs.")
    args = parser.parse_args()

    java_file = Path(args.java_file)
    if not java_file.is_absolute():
        java_file = (REPO_ROOT / java_file).resolve()
    if not java_file.exists():
        print(f"java file not found: {java_file}", file=sys.stderr)
        return 2

    exit_code, output = run_openjml(java_file)
    well_formed, fatal, tolerated = classify(java_file, exit_code, output)

    tooling = any(r.startswith("__tooling__") for r in fatal)
    report = render_report(java_file, exit_code, well_formed and not tooling, fatal, tolerated)

    if args.log_dir:
        log_dir = Path(args.log_dir)
        log_dir.mkdir(parents=True, exist_ok=True)
        (log_dir / "wellformed_openjml.log").write_text(output, encoding="utf-8")
        (log_dir / "wellformed_classification.md").write_text(report, encoding="utf-8")

    print(report, end="")

    if tooling:
        return 2
    return 0 if well_formed else 1


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Unified verify artifact audit for source integrity and proof bypasses.

This checker is intended to run outside the agent-visible prompt. It combines:

* proof/source artifact checks from ``check_qcp_cheating.py``;
* basic artifact shape and executable-source integrity checks.

It accepts one or more verify workspace/result directories and returns findings
grouped by audit class. A nonzero exit code means at least one error finding was
found, unless ``--no-fail`` is used.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys
from typing import Any, Iterable

import check_qcp_cheating


WORKSPACE_RE = re.compile(r"^verify_\d{8}_\d+_(?P<name>[A-Za-z0-9_]+)$")
STANDARD_GENERATED_RE = re.compile(r".*_(goal|proof_auto|proof_manual|goal_check)\.v$")
TARGET_GENERATED_SUFFIXES = ("goal", "proof_auto", "proof_manual", "goal_check")
SYEXEC_OWNED_SUFFIXES = ("goal", "proof_auto", "goal_check")


def normalize_c_without_annotations(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    text = re.sub(r"//.*", "", text)
    return re.sub(r"\s+", "", text)


def infer_case_name(workspace: Path) -> str:
    match = WORKSPACE_RE.match(workspace.name)
    if match:
        return match.group("name")
    return workspace.name


def finding(
    *,
    case: str,
    group: str,
    category: str,
    severity: str,
    file: str,
    line: int = 0,
    snippet: str = "",
    message: str,
) -> dict[str, Any]:
    return {
        "case": case,
        "group": group,
        "category": category,
        "severity": severity,
        "file": file,
        "line": line,
        "snippet": re.sub(r"\s+", " ", snippet).strip()[:700],
        "message": message,
    }


def one_or_none(paths: Iterable[Path]) -> Path | None:
    paths = sorted(paths)
    if len(paths) == 1:
        return paths[0]
    return None


def original_c_path(workspace: Path, case: str) -> Path | None:
    preferred = workspace / "original" / f"{case}.c"
    if preferred.exists():
        return preferred
    return one_or_none((workspace / "original").glob("*.c"))


def verified_c_path(workspace: Path) -> Path | None:
    annotated_dir = workspace / "annotated"
    preferred = annotated_dir / f"{workspace.name}.c"
    if preferred.exists():
        return preferred
    return one_or_none(annotated_dir.glob("*.c"))


def generated_dir(workspace: Path) -> Path:
    return workspace / "coq" / "generated"


def infer_generated_stem(gendir: Path, case: str) -> str:
    preferred = gendir / f"{case}_proof_manual.v"
    if preferred.exists():
        return case
    manuals = sorted(gendir.glob("*_proof_manual.v"))
    if len(manuals) == 1:
        return manuals[0].name[:-len("_proof_manual.v")]
    return case


def normalized_generated_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace").replace("\r\n", "\n")


def generated_proof_files(workspace: Path) -> list[tuple[Path, bool]]:
    """Return ``(path, flag_stubs)`` proof-like files to audit.

    ``proof_auto.v`` stubs are normal QCP output, so only assumptions/imports are
    flagged there. ``goal.v`` is excluded because QCP emits witness axioms in it
    by convention; ``proof_manual.v``, ``goal_check.v``, and nonstandard helper
    files carry no such exemption.
    """
    gendir = generated_dir(workspace)
    if not gendir.exists():
        return []

    proof_files: list[tuple[Path, bool]] = []
    for path in sorted(gendir.glob("*.v")):
        name = path.name
        if name.endswith("_goal.v"):
            continue
        if name.endswith("_proof_auto.v"):
            proof_files.append((path, False))
            continue
        if name.endswith("_proof_manual.v") or name.endswith("_goal_check.v"):
            proof_files.append((path, True))
            continue
        if not STANDARD_GENERATED_RE.match(name):
            proof_files.append((path, True))
    return proof_files


def normalize_qcp_finding(raw: dict[str, Any], *, case: str) -> dict[str, Any]:
    category = str(raw.get("category", "proof_artifact"))
    if category in {"proof_stub", "manual_axiom"}:
        group = "proof_bypass"
    elif category == "contract_weakening":
        group = "source_integrity"
    elif category == "forbidden_import":
        group = "import_review"
    else:
        group = "proof_artifact"
    return finding(
        case=case,
        group=group,
        category=category,
        severity=str(raw.get("severity", "error")),
        file=str(raw.get("file", "")),
        line=int(raw.get("line", 0) or 0),
        snippet=str(raw.get("snippet", "")),
        message=str(raw.get("message", "")),
    )


def scan_source_artifacts(workspace: Path, case: str) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    original = original_c_path(workspace, case)
    verified = verified_c_path(workspace)

    if original is None:
        findings.append(finding(
            case=case,
            group="artifact_shape",
            category="missing_original_c",
            severity="error",
            file=str(workspace / "original"),
            message="Missing unique original C artifact.",
        ))
    if verified is None:
        findings.append(finding(
            case=case,
            group="artifact_shape",
            category="missing_verified_c",
            severity="error",
            file=str(workspace / "annotated"),
            message="Missing unique verified/annotated C artifact.",
        ))

    if original is None or verified is None:
        return findings

    original_text = original.read_text(encoding="utf-8", errors="replace")
    verified_text = verified.read_text(encoding="utf-8", errors="replace")
    for raw in check_qcp_cheating.scan_contract_weakening(original_text, verified_text):
        findings.append(normalize_qcp_finding(raw, case=case))

    if normalize_c_without_annotations(original_text) != normalize_c_without_annotations(verified_text):
        findings.append(finding(
            case=case,
            group="source_integrity",
            category="executable_c_changed",
            severity="error",
            file=str(verified),
            message="Verified C changes executable code after removing comments/QCP annotations.",
        ))

    return findings


def scan_proof_artifacts(workspace: Path, case: str) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    gendir = generated_dir(workspace)
    if not gendir.exists():
        return [finding(
            case=case,
            group="artifact_shape",
            category="missing_generated_dir",
            severity="error",
            file=str(gendir),
            message="Missing generated Coq artifact directory.",
        )]

    stem = infer_generated_stem(gendir, case)
    for suffix in TARGET_GENERATED_SUFFIXES:
        if (gendir / f"{stem}_{suffix}.v").exists():
            continue
        findings.append(finding(
            case=case,
            group="artifact_shape",
            category="missing_target_generated_artifact",
            severity="error",
            file=str(gendir / f"{stem}_{suffix}.v"),
            message=f"Missing unique target generated artifact for suffix {suffix}.",
        ))

    for path, flag_stubs in generated_proof_files(workspace):
        text = path.read_text(encoding="utf-8", errors="replace")
        for raw in check_qcp_cheating.scan_proof_file(text, path.name, flag_stubs=flag_stubs):
            normalized = normalize_qcp_finding(raw, case=case)
            normalized["file"] = str(path)
            findings.append(normalized)

    return findings


def scan_generated_freshness(
    submitted_dir: Path,
    fresh_dir: Path,
    *,
    case: str,
    function_name: str | None = None,
) -> list[dict[str, Any]]:
    """Compare symexec-owned target artifacts against a fresh symexec run.

    ``proof_manual.v`` is deliberately excluded because it is the manual proof
    file. The other target files must be the runner-generated output for the
    final annotated C, not hand-edited artifacts.
    """
    findings: list[dict[str, Any]] = []
    stem = function_name or case
    for suffix in SYEXEC_OWNED_SUFFIXES:
        submitted = submitted_dir / f"{stem}_{suffix}.v"
        fresh = fresh_dir / f"{stem}_{suffix}.v"
        if not submitted.exists():
            findings.append(finding(
                case=case,
                group="generated_freshness",
                category="missing_submitted_generated_artifact",
                severity="error",
                file=str(submitted),
                message=f"Missing submitted symexec-owned artifact {submitted.name}.",
            ))
            continue
        if not fresh.exists():
            findings.append(finding(
                case=case,
                group="generated_freshness",
                category="missing_fresh_generated_artifact",
                severity="error",
                file=str(fresh),
                message=f"Fresh symexec did not produce expected artifact {fresh.name}.",
            ))
            continue
        if normalized_generated_text(submitted) != normalized_generated_text(fresh):
            findings.append(finding(
                case=case,
                group="generated_freshness",
                category="modified_symexec_owned_artifact",
                severity="error",
                file=str(submitted),
                message=(
                    f"{submitted.name} differs from fresh symexec output for the final "
                    "annotated C. Only the manual proof artifact may contain manual edits."
                ),
            ))
    return findings


def scan_workspace(workspace: Path) -> dict[str, Any]:
    workspace = workspace.resolve()
    case = infer_case_name(workspace)
    findings: list[dict[str, Any]] = []
    findings.extend(scan_source_artifacts(workspace, case))
    findings.extend(scan_proof_artifacts(workspace, case))
    return {
        "workspace": str(workspace),
        "case": case,
        "findings": findings,
        "summary": summarize(findings),
    }


def discover_workspaces(paths: Iterable[Path]) -> list[Path]:
    workspaces: set[Path] = set()
    for path in paths:
        if path.is_file():
            continue
        if not path.is_dir():
            continue
        if WORKSPACE_RE.match(path.name) and ((path / "logs").exists() or (path / "coq").exists()):
            workspaces.add(path)
            continue
        for candidate in path.glob("verify_*"):
            if candidate.is_dir() and WORKSPACE_RE.match(candidate.name):
                workspaces.add(candidate)
    return sorted(workspaces)


def summarize(findings: list[dict[str, Any]]) -> dict[str, Any]:
    errors = [f for f in findings if f.get("severity") == "error"]
    warnings = [f for f in findings if f.get("severity") == "warning"]
    by_group: dict[str, int] = {}
    by_category: dict[str, int] = {}
    for item in findings:
        by_group[str(item.get("group", "?"))] = by_group.get(str(item.get("group", "?")), 0) + 1
        by_category[str(item.get("category", "?"))] = by_category.get(str(item.get("category", "?")), 0) + 1
    return {
        "total": len(findings),
        "errors": len(errors),
        "warnings": len(warnings),
        "groups": dict(sorted(by_group.items())),
        "categories": dict(sorted(by_category.items())),
        "clean": len(errors) == 0,
    }


def aggregate(results: list[dict[str, Any]]) -> dict[str, Any]:
    findings = [finding for result in results for finding in result["findings"]]
    summary = summarize(findings)
    summary["workspaces"] = len(results)
    summary["clean_workspaces"] = sum(1 for result in results if result["summary"]["clean"])
    return summary


def print_text(results: list[dict[str, Any]]) -> None:
    summary = aggregate(results)
    print(
        "Unified verify audit: "
        f"workspaces={summary['workspaces']} findings={summary['total']} "
        f"errors={summary['errors']} warnings={summary['warnings']} "
        f"clean={summary['errors'] == 0}"
    )
    if summary["groups"]:
        print("Groups:")
        for group, count in summary["groups"].items():
            print(f"- {group}: {count}")
    for result in results:
        if not result["findings"]:
            continue
        print(f"\n## {result['case']}")
        for item in result["findings"]:
            print(
                f"- {item['severity']} {item['group']}/{item['category']} "
                f"{item['file']}:{item['line']}\n"
                f"  {item['message']}\n"
                f"  {item['snippet']}"
            )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Unified verify artifact anti-cheating audit.")
    parser.add_argument("paths", nargs="+", help="Verify workspace/result directories.")
    parser.add_argument(
        "--fresh-generated",
        help="Optional fresh symexec generated directory to compare against one workspace's submitted artifacts.",
    )
    parser.add_argument("--function-name", help="Target function stem for --fresh-generated comparison.")
    parser.add_argument("--json", action="store_true", help="Emit JSON.")
    parser.add_argument("--no-fail", action="store_true", help="Always exit 0.")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    workspaces = discover_workspaces([Path(p) for p in args.paths])
    if args.fresh_generated and len(workspaces) != 1:
        raise SystemExit("--fresh-generated requires exactly one discovered workspace")
    results = [scan_workspace(path) for path in workspaces]
    if args.fresh_generated:
        result = results[0]
        case = result["case"]
        fresh_findings = scan_generated_freshness(
            generated_dir(Path(result["workspace"])),
            Path(args.fresh_generated),
            case=case,
            function_name=args.function_name or case,
        )
        result["findings"].extend(fresh_findings)
        result["summary"] = summarize(result["findings"])
    summary = aggregate(results)
    if args.json:
        json.dump({"summary": summary, "results": results}, sys.stdout, indent=2, ensure_ascii=False)
        sys.stdout.write("\n")
    else:
        print_text(results)
    if args.no_fail:
        return 0
    return 1 if summary["errors"] else 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Populate annotated_input/humaneval from input/humaneval plus QCP annotations.

Policy:
1. Copy every top-level file from input/humaneval into annotated_input/humaneval.
2. For each pNNN_*.c, choose a matching QCP_examples/humaneval/*/C_N.c with
   annotations and overwrite only the aligned annotated C.
3. Keep the CAV input .v as the primary paired pNNN_*.v. Also copy QCP helper
   .v files such as coins_N.v and their loaded spec files, because many QCP
   annotations import those helpers.
"""
from __future__ import annotations

from pathlib import Path
import json
import re
import shutil


REPO = Path("/home/yangfp/CAV/C/CAV")
INPUT = REPO / "input" / "humaneval"
DEST = REPO / "annotated_input" / "humaneval"
QCP_HUMANEVAL = Path("/home/yangfp/QualifiedCProgramming/QCP_examples/humaneval")

PRIORITY = [
    "Int",
    "IntArray",
    "String",
    "IntClaude",
    "IntArrayClaude",
    "StringClaude",
    "multi_dimensional_arrays",
    "c_files",
]
HELPER_TARGET_EXCLUDE = {
    "malloc",
    "malloc_int_array",
    "malloc_char_array",
    "malloc_int_array_struct",
    "strlen",
}


FUNC_DEF_RE = re.compile(
    r"(?m)^\s*(?:[A-Za-z_][A-Za-z0-9_]*\s+)+\*?\s*([A-Za-z_][A-Za-z0-9_]*)\s*\([^;{}]*\)\s*(?:/\*@.*?\*/\s*)?\{",
    re.S,
)


def problem_number(stem: str) -> int:
    m = re.match(r"p(\d+)_", stem)
    if not m:
        raise ValueError(f"bad humaneval problem stem: {stem}")
    return int(m.group(1))


def choose_qcp_c(n: int) -> Path | None:
    candidates = sorted(QCP_HUMANEVAL.glob(f"*/C_{n}.c"))
    scored: list[tuple[int, int, Path]] = []
    for path in candidates:
        text = path.read_text(encoding="utf-8", errors="replace")
        if "/*@" not in text:
            continue
        category = path.parent.name
        priority = PRIORITY.index(category) if category in PRIORITY else 999
        has_full_proof = all(
            (path.parent / f"C_{n}_{suffix}.v").exists()
            for suffix in ("goal", "proof_auto", "proof_manual", "goal_check")
        )
        scored.append((0 if has_full_proof else 1, priority, path))
    if not scored:
        return None
    scored.sort()
    return scored[0][2]


def target_function_name(text: str) -> str | None:
    names = [m.group(1) for m in FUNC_DEF_RE.finditer(text)]
    names = [name for name in names if name not in HELPER_TARGET_EXCLUDE]
    return names[-1] if names else None


def align_c_text(text: str, old_func: str | None, new_func: str) -> str:
    text = re.sub(r'#\s*include\s+"(?:\.\./)+([^"/]+)"', r'#include "\1"', text)
    if old_func and old_func != new_func:
        text = re.sub(rf"\b{re.escape(old_func)}\b", new_func, text)
    return text


LOAD_RE = re.compile(r'^\s*Load\s+"([^"]+)"\s*\.', re.M)
REQ_RE = re.compile(r"^\s*Require\s+Import\s+([A-Za-z0-9_ ]+)\s*\.", re.M)
FROM_REQ_RE = re.compile(r"^\s*From\s+[A-Za-z0-9_.]+\s+Require\s+(?:Import|Export)\s+([A-Za-z0-9_ ]+)\s*\.", re.M)


def copy_qcp_v_closure(source: Path, copied: set[Path]) -> list[str]:
    logs: list[str] = []
    if not source.exists() or source in copied:
        return logs
    copied.add(source)
    target = DEST / source.name
    shutil.copy2(source, target)
    logs.append(str(target.relative_to(DEST)))

    text = source.read_text(encoding="utf-8", errors="replace")
    for load in LOAD_RE.findall(text):
        raw = (source.parent / load).with_suffix(".v")
        if raw.exists():
            try:
                rel = raw.resolve().relative_to(QCP_HUMANEVAL.resolve())
            except ValueError:
                continue
            target_load = DEST / rel
            target_load.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(raw, target_load)
            logs.append(str(target_load.relative_to(DEST)))
    for group in REQ_RE.findall(text) + FROM_REQ_RE.findall(text):
        for module in group.split():
            local = source.parent / f"{module}.v"
            if local.exists():
                logs.extend(copy_qcp_v_closure(local, copied))
    return logs


def copy_reference_proofs(n: int, qcp_dir: Path, dest_stem: str) -> list[str]:
    proof_dir = DEST / "proofs" / dest_stem
    proof_dir.mkdir(parents=True, exist_ok=True)
    copied: list[str] = []
    for suffix in ("goal", "proof_auto", "proof_manual", "goal_check"):
        src = qcp_dir / f"C_{n}_{suffix}.v"
        if not src.exists():
            continue
        dst = proof_dir / f"{dest_stem}_{suffix}.v"
        text = src.read_text(encoding="utf-8", errors="replace")
        text = re.sub(rf"\bC_{n}\b", dest_stem, text)
        dst.write_text(text, encoding="utf-8")
        copied.append(str(dst.relative_to(DEST)))
    return copied


def main() -> int:
    DEST.mkdir(parents=True, exist_ok=True)

    base_copied = []
    for source in sorted(INPUT.iterdir()):
        if source.is_file():
            target = DEST / source.name
            shutil.copy2(source, target)
            base_copied.append(str(target.relative_to(DEST)))

    manifest = {
        "base_source": str(INPUT),
        "annotation_source": str(QCP_HUMANEVAL),
        "base_copied": base_copied,
        "problems": [],
        "missing_annotation": [],
    }

    copied_qcp_v: set[Path] = set()
    for input_c in sorted(INPUT.glob("p*.c")):
        stem = input_c.stem
        n = problem_number(stem)
        qcp_c = choose_qcp_c(n)
        if qcp_c is None:
            manifest["missing_annotation"].append(stem)
            continue
        qcp_text = qcp_c.read_text(encoding="utf-8", errors="replace")
        old_func = target_function_name(qcp_text)
        aligned = align_c_text(qcp_text, old_func, stem)
        (DEST / input_c.name).write_text(aligned, encoding="utf-8")

        copied_v = []
        for qcp_v in sorted(qcp_c.parent.glob(f"coins_{n}.v")):
            copied_v.extend(copy_qcp_v_closure(qcp_v, copied_qcp_v))
        proofs = copy_reference_proofs(n, qcp_c.parent, stem)
        manifest["problems"].append(
            {
                "name": stem,
                "qcp_c": str(qcp_c),
                "old_function": old_func,
                "new_function": stem,
                "qcp_v_helpers": sorted(set(copied_v)),
                "reference_proofs": proofs,
            }
        )

    manifest_path = DEST / "_qcp_humaneval_import_manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"copied base files: {len(base_copied)}")
    print(f"annotated problems: {len(manifest['problems'])}")
    print(f"missing annotations: {len(manifest['missing_annotation'])}")
    print(f"manifest: {manifest_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

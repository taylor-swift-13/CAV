#!/usr/bin/env python3
"""Import QCP humaneval proofs into ground_truth, aligned to CAV inputs.

The ground truth source is /home/yangfp/QualifiedCProgramming/QCP_examples/humaneval.
For each input/humaneval/pNNN_*.c, this script selects a QCP C_N proof bundle
with a non-stub manual proof and writes one workspace-shaped directory:

  ground_truth/pNNN_name/
    pNNN_name.c
    pNNN_name_goal.v
    pNNN_name_proof_auto.v
    pNNN_name_proof_manual.v
    pNNN_name_goal_check.v

The C file and specifications are treated as input/humaneval-owned. QCP files
are only used as a proof/template source; helper dependencies are not imported
into ground_truth.
"""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import shutil


REPO = Path("/home/yangfp/CAV/C/CAV")
INPUT = REPO / "input" / "humaneval"
GROUND_TRUTH = REPO / "ground_truth"
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

CONTRACT_BLOCK_RE = re.compile(r"/\*@(.*?)\*/", re.S)
LOAD_RE = re.compile(r'^\s*Load\s+"([^"]+)"\s*\.', re.M)
REQ_RE = re.compile(r"^\s*Require\s+(?:Import|Export)\s+([A-Za-z0-9_ ]+)\s*\.", re.M)
FROM_REQ_RE = re.compile(r"^\s*From\s+[A-Za-z0-9_.]+\s+Require\s+(?:Import|Export)\s+([A-Za-z0-9_ ]+)\s*\.", re.M)
MANUAL_OBLIGATION_RE = re.compile(
    r"(?<![A-Za-z_])(Admitted|Abort|admit|give_up)(?![A-Za-z_])|^\s*(Axiom|Hypothesis|Parameter|Conjecture)\s",
    re.M,
)


@dataclass(frozen=True)
class ProofSet:
    label: str
    goal: Path
    proof_auto: Path
    proof_manual: Path
    goal_check: Path


@dataclass(frozen=True)
class Candidate:
    c_path: Path
    proof_set: ProofSet
    old_function: str | None
    contract_matches_input: bool
    executable_matches_input: bool


def problem_number(stem: str) -> int:
    m = re.match(r"p(\d+)_", stem)
    if not m:
        raise ValueError(f"bad humaneval stem: {stem}")
    return int(m.group(1))


def normalize_ws(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def normalize_c_without_annotations(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    text = re.sub(r"//.*", "", text)
    return re.sub(r"\s+", "", text)


def extract_contract_specs(text: str) -> list[str]:
    specs: list[str] = []
    for body in CONTRACT_BLOCK_RE.findall(text):
        if re.search(r"\bEnsure\b", body):
            specs.append(normalize_ws(body))
    return specs


def align_includes_and_name(text: str, old_func: str | None, new_func: str) -> str:
    text = re.sub(r'#\s*include\s+"(?:\.\./)+([^"/]+)"', r'#include "\1"', text)
    if old_func and old_func != new_func:
        text = re.sub(rf"\b{re.escape(old_func)}\b", new_func, text)
    return text


def contract_name_before(text: str, block_start: int) -> str | None:
    prefix = text[:block_start]
    cut = max(prefix.rfind(";"), prefix.rfind("{"), prefix.rfind("}"), prefix.rfind("*/"))
    context = prefix[cut + 1 :]
    match = re.search(r"([A-Za-z_][A-Za-z0-9_]*)\s*\([^;{}]*\)\s*$", context, re.S)
    return match.group(1) if match else None


def function_contracts_by_name(text: str) -> dict[str, str]:
    contracts: dict[str, str] = {}
    for match in CONTRACT_BLOCK_RE.finditer(text):
        body = match.group(1)
        if not re.search(r"\bEnsure\b", body):
            continue
        name = contract_name_before(text, match.start())
        if name:
            contracts[name] = match.group(0)
    return contracts


def target_function_name(text: str) -> str | None:
    names = [
        name
        for name in function_contracts_by_name(text)
        if name not in HELPER_TARGET_EXCLUDE
    ]
    return names[-1] if names else None


def replace_function_contracts(text: str, input_text: str) -> str:
    replacements = function_contracts_by_name(input_text)
    pieces: list[str] = []
    last = 0
    for match in CONTRACT_BLOCK_RE.finditer(text):
        pieces.append(text[last : match.start()])
        body = match.group(1)
        name = contract_name_before(text, match.start())
        if name and re.search(r"\bEnsure\b", body) and name in replacements:
            pieces.append(replacements[name])
        else:
            pieces.append(match.group(0))
        last = match.end()
    pieces.append(text[last:])
    return "".join(pieces)


def manual_is_complete(path: Path) -> bool:
    text = path.read_text(encoding="utf-8", errors="replace")
    return MANUAL_OBLIGATION_RE.search(text) is None


def proof_sets_for(c_path: Path, n: int) -> list[ProofSet]:
    variants = [
        ("proof", "proof_auto", "proof_manual"),
        ("plain", "auto", "manual"),
    ]
    proof_sets: list[ProofSet] = []
    for label, auto_suffix, manual_suffix in variants:
        goal = c_path.parent / f"C_{n}_goal.v"
        proof_auto = c_path.parent / f"C_{n}_{auto_suffix}.v"
        proof_manual = c_path.parent / f"C_{n}_{manual_suffix}.v"
        goal_check = c_path.parent / f"C_{n}_goal_check.v"
        if all(path.exists() for path in (goal, proof_auto, proof_manual, goal_check)):
            if manual_is_complete(proof_manual):
                proof_sets.append(ProofSet(label, goal, proof_auto, proof_manual, goal_check))
    return proof_sets


def candidate_score(candidate: Candidate, input_text: str) -> tuple[int, int, int, str]:
    category = candidate.c_path.parent.name
    priority = PRIORITY.index(category) if category in PRIORITY else 999
    return (
        0 if candidate.contract_matches_input else 1,
        0 if candidate.executable_matches_input else 1,
        priority,
        str(candidate.c_path),
    )


def choose_candidate(stem: str, input_text: str) -> Candidate:
    n = problem_number(stem)
    candidates: list[Candidate] = []
    for c_path in sorted(QCP_HUMANEVAL.glob(f"*/C_{n}.c")):
        qcp_text = c_path.read_text(encoding="utf-8", errors="replace")
        if "/*@" not in qcp_text:
            continue
        old_func = target_function_name(qcp_text)
        aligned = align_includes_and_name(qcp_text, old_func, stem)
        aligned = replace_function_contracts(aligned, input_text)
        contract_matches = extract_contract_specs(aligned) == extract_contract_specs(input_text)
        executable_matches = normalize_c_without_annotations(aligned) == normalize_c_without_annotations(input_text)
        for proof_set in proof_sets_for(c_path, n):
            candidates.append(
                Candidate(
                    c_path=c_path,
                    proof_set=proof_set,
                    old_function=old_func,
                    contract_matches_input=contract_matches,
                    executable_matches_input=executable_matches,
                )
            )
    if not candidates:
        raise RuntimeError(f"no complete QCP proof candidate for {stem}")
    return sorted(candidates, key=lambda c: candidate_score(c, input_text))[0]


def problem_number_from_c_name(path: Path) -> int:
    m = re.match(r"C_(\d+)\.c$", path.name)
    if not m:
        raise ValueError(f"bad QCP C name: {path}")
    return int(m.group(1))


def rewrite_v_text(text: str, *, n: int, stem: str, old_func: str | None, proof_set: ProofSet) -> str:
    if old_func and old_func != stem:
        text = text.replace(old_func, stem)
    text = re.sub(rf"^\s*Require\s+Import\s+coins_{n}\s*\.\s*\n", "", text, flags=re.M)
    text = re.sub(rf"\bC_{n}_proof_auto\b", f"{stem}_proof_auto", text)
    text = re.sub(rf"\bC_{n}_proof_manual\b", f"{stem}_proof_manual", text)
    text = re.sub(rf"\bC_{n}_auto\b", f"{stem}_proof_auto", text)
    text = re.sub(rf"\bC_{n}_manual\b", f"{stem}_proof_manual", text)
    text = re.sub(rf"\bC_{n}_goal\b", f"{stem}_goal", text)
    text = re.sub(rf"\bC_{n}\b", stem, text)
    return text


def copy_workspace_bundle(stem: str, input_text: str, candidate: Candidate, case_dir: Path) -> dict[str, list[str] | str]:
    n = problem_number(stem)
    annotation_path = case_dir / f"{stem}.c"
    annotation_path.write_text(input_text, encoding="utf-8")

    proof_sources = {
        "goal": candidate.proof_set.goal,
        "proof_auto": candidate.proof_set.proof_auto,
        "proof_manual": candidate.proof_set.proof_manual,
        "goal_check": candidate.proof_set.goal_check,
    }
    proof_files: list[str] = []
    for suffix, source in proof_sources.items():
        target = case_dir / f"{stem}_{suffix}.v"
        text = source.read_text(encoding="utf-8", errors="replace")
        text = rewrite_v_text(text, n=n, stem=stem, old_func=candidate.old_function, proof_set=candidate.proof_set)
        target.write_text(text, encoding="utf-8")
        proof_files.append(str(target.relative_to(GROUND_TRUTH)))

    dep_files: list[str] = []
    return {
        "annotation": str(annotation_path.relative_to(GROUND_TRUTH)),
        "proof_files": proof_files,
        "deps": dep_files,
    }


def copy_qcp_dependency_closure(qcp_dir: Path, n: int, dest: Path) -> list[str]:
    copied: list[str] = []
    seen: set[Path] = set()

    def copy_one(source: Path) -> None:
        resolved = source.resolve()
        if resolved in seen or not source.exists():
            return
        seen.add(resolved)
        target = dest / source.name
        shutil.copy2(source, target)
        copied.append(str(target.relative_to(GROUND_TRUTH)))
        text = source.read_text(encoding="utf-8", errors="replace")
        for load in LOAD_RE.findall(text):
            load_path = (source.parent / load).with_suffix(".v")
            if load_path.exists():
                try:
                    rel = load_path.resolve().relative_to(QCP_HUMANEVAL.resolve())
                except ValueError:
                    rel = Path(load_path.name)
                load_target = dest / rel
                load_target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(load_path, load_target)
                copied.append(str(load_target.relative_to(GROUND_TRUTH)))
        for group in REQ_RE.findall(text) + FROM_REQ_RE.findall(text):
            for module in group.split():
                local = source.parent / f"{module}.v"
                if local.exists():
                    copy_one(local)

    for source in sorted(qcp_dir.glob(f"coins_{n}.v")):
        copy_one(source)
    return sorted(set(copied))


def write_verify_script(case_dir: Path, stem: str, candidate: Candidate) -> str:
    n = problem_number(stem)
    category_rel = candidate.c_path.parent.relative_to(QCP_HUMANEVAL)
    proof_set = candidate.proof_set
    auto_name = proof_set.proof_auto.name
    manual_name = proof_set.proof_manual.name
    script = f"""#!/usr/bin/env bash
set -euo pipefail
cd /home/yangfp/QualifiedCProgramming/QCP_examples/humaneval/{category_rel}
COQ_ARGS=(
  -R ../../../SeparationLogic/SeparationLogic SimpleC.SL
  -R ../../../SeparationLogic/unifysl Logic
  -R ../../../SeparationLogic/sets SetsClass
  -R ../../../SeparationLogic/compcert_lib compcert.lib
  -R ../../../SeparationLogic/auxlibs AUXLib
  -R ../../../SeparationLogic/examples SimpleC.EE
  -R ../../../SeparationLogic/stdlib SimpleC.StdLib
  -R . SimpleC.EE
  -R ../../../SeparationLogic/StrategyLib SimpleC.StrategyLib
  -R ../../../SeparationLogic/Common SimpleC.Common
  -R ../../../SeparationLogic/fixedpoints FP
  -R ../../../SeparationLogic/MonadLib MonadLib
  -R ../../../SeparationLogic/listlib ListLib
)
for dep in coins_{n}.v; do
  [[ -f "$dep" ]] && coqc "${{COQ_ARGS[@]}}" "$dep"
done
coqc "${{COQ_ARGS[@]}}" C_{n}_goal.v
coqc "${{COQ_ARGS[@]}}" {auto_name}
coqc "${{COQ_ARGS[@]}}" {manual_name}
coqc "${{COQ_ARGS[@]}}" C_{n}_goal_check.v
"""
    target = case_dir / "verify_qcp_original.sh"
    target.write_text(script, encoding="utf-8")
    target.chmod(0o755)
    return str(target.relative_to(GROUND_TRUTH))


def main() -> int:
    if GROUND_TRUTH.exists():
        shutil.rmtree(GROUND_TRUTH)
    GROUND_TRUTH.mkdir(parents=True, exist_ok=True)

    imported = 0
    missing: list[dict[str, str]] = []

    for input_c in sorted(INPUT.glob("p*.c")):
        stem = input_c.stem
        input_text = input_c.read_text(encoding="utf-8", errors="replace")
        case_dir = GROUND_TRUTH / stem
        case_dir.mkdir(parents=True, exist_ok=True)

        try:
            candidate = choose_candidate(stem, input_text)
        except Exception as exc:  # keep going and make the miss explicit
            (case_dir / "import_error.log").write_text(str(exc) + "\n", encoding="utf-8")
            missing.append({"name": stem, "error": str(exc)})
            continue

        copy_workspace_bundle(stem, input_text, candidate, case_dir)
        imported += 1

    print(f"imported: {imported}")
    print(f"missing: {len(missing)}")
    for item in missing:
        print(f"missing {item['name']}: {item['error']}")
    return 0 if not missing else 1


if __name__ == "__main__":
    raise SystemExit(main())

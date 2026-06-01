#!/usr/bin/env python3
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import agent_config
import agent_metrics
import check_qcp_cheating


REPO_ROOT = Path(__file__).resolve().parents[1]
import coq_runner

DEFAULT_SKILL = REPO_ROOT / "skills" / "verify" / "SKILL.md"
OUTPUT_ROOT = REPO_ROOT / "output"
EXAMPLES_ROOT = REPO_ROOT / "experiences" / "end-end"
DEFAULT_MODEL = "gpt-5.4"
DEFAULT_CLAUDE_MODEL = "sonnet"
DEFAULT_REASONING_EFFORT = "medium"

# Agent-facing rules live in skills/verify/SKILL.md (see §4.0 read/write
# boundaries, §4.3/§4.4 proof-manual-only completion, §4.5a-§4.5e workflow).
# This script's prompts pass paths + per-run context and refer to the skill.

NOISE_PATTERNS = [
    "WARNING: proceeding, even though we could not update PATH: Read-only file system",
    "failed to renew cache TTL: Read-only file system",
    "failed to record rollout items: failed to queue rollout items: channel closed",
    "failed to connect to websocket: IO error: Connection reset by peer",
]


def timestamp_now() -> str:
    return dt.datetime.now().strftime("%Y%m%d_%H%M%S")


def iso_now() -> str:
    return dt.datetime.now().astimezone().strftime("%Y-%m-%d %H:%M:%S %z")


def stem_from_input(input_path: Path) -> str:
    return input_path.stem


def ensure_parent(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


def emit_log(message: str) -> None:
    print(f"[verify] {message}", flush=True)


def build_agent_env(logs_dir: Path) -> dict[str, str]:
    env = os.environ.copy()
    cache_dir = logs_dir / ".agent_cache"
    state_dir = logs_dir / ".state"
    data_dir = logs_dir / ".data"
    config_dir = logs_dir / ".config"
    tmp_dir = logs_dir / ".tmp"
    cache_dir.mkdir(parents=True, exist_ok=True)
    state_dir.mkdir(parents=True, exist_ok=True)
    data_dir.mkdir(parents=True, exist_ok=True)
    config_dir.mkdir(parents=True, exist_ok=True)
    tmp_dir.mkdir(parents=True, exist_ok=True)
    env["XDG_CACHE_HOME"] = str(cache_dir)
    env["XDG_STATE_HOME"] = str(state_dir)
    env["XDG_DATA_HOME"] = str(data_dir)
    env["XDG_CONFIG_HOME"] = str(config_dir)
    env["TMPDIR"] = str(tmp_dir)
    env["TMP"] = str(tmp_dir)
    env["TEMP"] = str(tmp_dir)
    return env


def codex_supports_reasoning_effort(codex_bin: str, cwd: Path, env: dict[str, str]) -> bool:
    try:
        proc = subprocess.run(
            [codex_bin, "exec", "--help"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            cwd=cwd,
            env=env,
            timeout=10,
        )
    except (subprocess.SubprocessError, OSError):
        return False
    return "--reasoning-effort" in proc.stdout


def filter_stderr_in_place(stderr_log: Path) -> None:
    if not stderr_log.exists():
        return
    clean_lines = []
    for raw_line in stderr_log.read_text(encoding="utf-8", errors="replace").splitlines():
        if any(pattern in raw_line for pattern in NOISE_PATTERNS):
            continue
        clean_lines.append(raw_line)
    stderr_log.write_text("\n".join(clean_lines) + ("\n" if clean_lines else ""), encoding="utf-8")


def paired_input_v(input_path: Path) -> Path | None:
    candidate = input_path.with_suffix(".v")
    if candidate.exists():
        return candidate
    return None


def _input_lines(input_path: Path, input_v_path: Path | None, function_name: str, workspace_path: Path, annotated_c_path: Path) -> str:
    input_v = f"`{input_v_path}`" if input_v_path else "`<not provided>`"
    return (
        f"- Input C: `{input_path}`\n"
        f"- Optional input V: {input_v}\n"
        f"- Target function: `{function_name}`\n"
        f"- Workspace: `{workspace_path}`\n"
        f"- Active annotated C: `{annotated_c_path}`\n"
    )


def build_prompt(
    skill_path: Path,
    input_path: Path,
    input_v_path: Path | None,
    function_name: str,
    workspace_path: Path,
    annotated_c_path: Path,
    attempt: int,
    restart_context: str | None = None,
) -> str:
    lines = [
        f"Follow this skill as the complete workflow: {skill_path}",
        "",
        "Inputs:",
        _input_lines(input_path, input_v_path, function_name, workspace_path, annotated_c_path).rstrip(),
    ]
    if attempt > 1:
        lines += ["", f"Attempt: {attempt} (retry — also follow MODE_RETRY.md per SKILL.md §4.5c)."]
    if restart_context:
        lines += ["", "Restart feedback:", restart_context.rstrip()]
    return "\n".join(lines) + "\n"


def build_proof_only_prompt(
    skill_path: Path,
    input_path: Path,
    input_v_path: Path | None,
    function_name: str,
    workspace_path: Path,
    annotated_c_path: Path,
    attempt: int,
    restart_context: str | None = None,
) -> str:
    lines = [
        f"Follow this skill as the complete workflow: {skill_path}",
        "",
        "Mode: proof-only (also follow MODE_PROOF_ONLY.md per SKILL.md §4.5c).",
        "",
        "Inputs:",
        _input_lines(input_path, input_v_path, function_name, workspace_path, annotated_c_path).rstrip(),
    ]
    if attempt > 1:
        lines += ["", f"Attempt: {attempt} (retry — also follow MODE_RETRY.md per SKILL.md §4.5c)."]
    if restart_context:
        lines += ["", "Restart feedback (must be addressed before finishing this verify run):", restart_context.rstrip()]
    return "\n".join(lines) + "\n"


def write_metrics(
    metrics_md_path: Path,
    *,
    status: str,
    attempts: int,
    last_agent_exit: int,
    start_iso: str,
    end_iso: str,
    wall_clock_seconds: float,
    model: str,
    reasoning_effort: str,
    usage: dict[str, int] | None,
    prompt_path: Path,
    stdout_jsonl: Path,
    stderr_log: Path,
    last_message_path: Path,
    input_c: Path,
    input_v: Path | None,
    export_examples: bool,
) -> None:
    lines = [
        "# Verify Metrics",
        "",
        "- Stage: `verify`",
        f"- Status: `{status}`",
        f"- Attempts: `{attempts}`",
        f"- Last agent exit code: `{last_agent_exit}`",
        f"- Start time: `{start_iso}`",
        f"- End time: `{end_iso}`",
        f"- Wall-clock time (seconds): `{wall_clock_seconds:.2f}`",
        f"- Model: `{model}`",
        f"- Reasoning effort: `{reasoning_effort}`",
        f"- Input C: `{input_c}`",
        f"- Input V: `{input_v if input_v else '<not provided>'}`",
        f"- Export examples: `{str(export_examples).lower()}`",
        f"- Prompt file: `{prompt_path}`",
        f"- Agent stdout: `{stdout_jsonl}`",
        f"- Agent stderr: `{stderr_log}`",
        f"- Agent last message: `{last_message_path}`",
    ]
    lines.extend(agent_metrics.usage_lines(
        usage, prompt_path=prompt_path, last_message_path=last_message_path))
    lines.extend(["- Experience updates: none", f"Final Result: {status}"])
    metrics_md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def update_issues_on_failure(issues_path: Path, stage: str, exit_code: int, stderr_log: Path) -> None:
    issues_path.parent.mkdir(parents=True, exist_ok=True)
    if issues_path.exists():
        existing = issues_path.read_text(encoding="utf-8").rstrip() + "\n\n"
    else:
        existing = "# Execution Issues\n\n"
    block = (
        "## External Codex Failure\n\n"
        f"- Stage: `{stage}`\n"
        f"- Exit code: `{exit_code}`\n"
        f"- Stderr log: `{stderr_log}`\n"
    )
    issues_path.write_text(existing + block, encoding="utf-8")


def append_continue(logs_dir: Path, kind: str, text: str) -> Path:
    logs_dir.mkdir(parents=True, exist_ok=True)
    path = logs_dir / "continue.md"
    header = "# Continue Log\n\n" if not path.exists() else ""
    stamp = iso_now()
    section = f"## {kind} @ {stamp}\n\n{text.rstrip()}\n\n"
    with path.open("a", encoding="utf-8") as f:
        if header:
            f.write(header)
        f.write(section)
    return path


def verify_retry_feedback(attempt: int, detail: str, workspace_path: Path, function_name: str) -> str:
    generated_dir = workspace_path / "coq" / "generated"
    return "\n".join([
        f"Verify attempt {attempt} failed the runner audit check.",
        "",
        f"- Detail: `{detail}`",
        f"- Generated dir: `{generated_dir}`",
        f"- Proof manual: `{generated_dir / f'{function_name}_proof_manual.v'}`",
        f"- Goal check: `{generated_dir / f'{function_name}_goal_check.v'}`",
        "",
        "Required next action: fix annotation/proof so symexec outputs exist, proof_manual has no admitted/axiom/abort placeholder, all generated Coq files compile, and annotated C preserves the original contract and executable implementation.",
    ])


def verify_workspace_completed(workspace_path: Path) -> tuple[bool, str]:
    metrics_md = metrics_path(workspace_path)
    if not metrics_md.exists():
        return False, f"missing_metrics:{metrics_md}"

    lines = metrics_md.read_text(encoding="utf-8", errors="replace").splitlines()
    saw_success = False
    saw_fail = False
    for raw_line in lines:
        # Tolerate markdown decoration the agent sometimes adds, e.g.
        # `**Final Result: Success (confirmed in round 7)**` — strip `*`/backticks
        # and match the marker as a substring rather than the whole line.
        cleaned = raw_line.replace("*", "").replace("`", "").strip()
        if "Final Result: Success" in cleaned:
            saw_success = True
        elif "Final Result: Fail" in cleaned:
            saw_fail = True

    if saw_success:
        return True, "metrics_contains_final_result_success"
    if saw_fail:
        return False, "metrics_contains_final_result_fail"
    return False, "metrics_missing_final_result"


def verify_proof_artifact_check(workspace_path: Path, function_name: str, input_v_path: Path | None) -> tuple[bool, str]:
    generated_dir = workspace_path / "coq" / "generated"
    required = [generated_dir / f"{function_name}_{suffix}.v" for suffix in ("goal", "proof_auto", "proof_manual", "goal_check")]
    missing = [str(path) for path in required if not path.exists()]
    if missing:
        return False, "missing_generated_files:" + ",".join(missing)

    if proof_manual_has_obligations(generated_dir, function_name):
        return False, f"proof_manual_has_obligations:{generated_dir / f'{function_name}_proof_manual.v'}"

    ok, compile_logs = compile_generated(workspace_path, function_name, input_v_path)
    log_path = workspace_path / "logs" / "audit_check_coqc.log"
    log_path.write_text("\n\n".join(compile_logs) + "\n", encoding="utf-8")
    if not ok:
        return False, f"audit_check_coqc_failed:{log_path}"

    return True, f"audit_check_success:{log_path}"


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalize_c_without_annotations(text: str) -> str:
    """Remove comments/QCP annotations and whitespace to compare executable C."""
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    text = re.sub(r"//.*", "", text)
    return re.sub(r"\s+", "", text)


def source_integrity_gate(
    *,
    workspace_path: Path,
    input_path: Path,
    input_v_path: Path | None,
    annotated_c_path: Path,
) -> tuple[bool, str]:
    """Deterministically reject verify runs that modify contract or implementation."""
    logs_dir = workspace_path / "logs"
    log_path = logs_dir / "source_integrity_gate.log"
    original_c = workspace_path / "original" / input_path.name
    details: list[str] = []

    if not original_c.exists():
        details.append(f"missing original C copy: {original_c}")
    elif file_sha256(original_c) != file_sha256(input_path):
        details.append(f"input C changed after verify bootstrap: {input_path}")

    if input_v_path is not None:
        original_v = workspace_path / "original" / input_v_path.name
        if not original_v.exists():
            details.append(f"missing original V copy: {original_v}")
        elif file_sha256(original_v) != file_sha256(input_v_path):
            details.append(f"input V changed after verify bootstrap: {input_v_path}")

    if not annotated_c_path.exists():
        details.append(f"missing annotated C: {annotated_c_path}")
    elif original_c.exists():
        original_text = original_c.read_text(encoding="utf-8", errors="replace")
        annotated_text = annotated_c_path.read_text(encoding="utf-8", errors="replace")

        findings = check_qcp_cheating.scan_contract_weakening(original_text, annotated_text)
        for finding in findings:
            details.append(f"{finding['category']}: {finding['message']}")

        if normalize_c_without_annotations(original_text) != normalize_c_without_annotations(annotated_text):
            details.append("annotated C changes executable implementation after removing comments/QCP annotations")

    if details:
        log_path.write_text("Source integrity gate failed:\n- " + "\n- ".join(details) + "\n", encoding="utf-8")
        return False, f"source_integrity_failed:{log_path}"

    log_path.write_text("Source integrity gate passed.\n", encoding="utf-8")
    return True, f"source_integrity_success:{log_path}"


def fingerprint_gate(workspace_path: Path, function_name: str) -> tuple[bool, str]:
    log_path = workspace_path / "logs" / "fingerprint_gate.log"
    path = workspace_path / "logs" / "workspace_fingerprint.json"
    details: list[str] = []
    if not path.exists():
        details.append(f"missing fingerprint: {path}")
    else:
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            details.append(f"fingerprint is not valid JSON: {exc}")
        else:
            required_strings = ("workspace", "stage", "input_c", "original_c", "annotated_c", "function_name", "semantic_description")
            for key in required_strings:
                value = data.get(key)
                if not isinstance(value, str) or not value.strip():
                    details.append(f"fingerprint field `{key}` must be a non-empty string")
            if data.get("stage") != "verify":
                details.append("fingerprint field `stage` must be `verify`")
            if data.get("function_name") != function_name:
                details.append(f"fingerprint function_name mismatch: {data.get('function_name')!r} != {function_name!r}")
            keywords = data.get("keywords")
            if not isinstance(keywords, dict) or not keywords:
                details.append("fingerprint field `keywords` must be a non-empty object")
            contract_source = data.get("contract_source")
            if contract_source != "contract_input_c":
                details.append("fingerprint field `contract_source` must be `contract_input_c`")
            if data.get("assume_contract_is_correct") is not True:
                details.append("fingerprint field `assume_contract_is_correct` must be true")

    if details:
        log_path.write_text("Fingerprint gate failed:\n- " + "\n- ".join(details) + "\n", encoding="utf-8")
        return False, f"fingerprint_failed:{log_path}"
    log_path.write_text("Fingerprint gate passed.\n", encoding="utf-8")
    return True, f"fingerprint_success:{log_path}"


def symexec_freshness_gate(
    *,
    workspace_path: Path,
    annotated_c_path: Path,
    function_name: str,
    timeout_seconds: int = 120,
) -> tuple[bool, str]:
    """Regenerate deterministic symexec artifacts from current annotated C and compare."""
    logs_dir = workspace_path / "logs"
    log_path = logs_dir / "symexec_freshness_gate.json"
    annotated_abs = annotated_c_path.resolve()
    annotated_hash = file_sha256(annotated_abs) if annotated_abs.exists() else ""
    current_dir = workspace_path / "coq" / "generated"
    fresh_root = logs_dir / "fresh_symexec"
    fresh_dir = fresh_root / "generated"
    if fresh_root.exists():
        shutil.rmtree(fresh_root)
    fresh_dir.mkdir(parents=True, exist_ok=True)

    logic_path = f"SimpleC.EE.CAV.{workspace_path.name}"
    cmd = [
        str(REPO_ROOT / "QualifiedCProgramming" / "linux-binary" / "symexec"),
        f"--goal-file={(fresh_dir / f'{function_name}_goal.v').resolve()}",
        f"--proof-auto-file={(fresh_dir / f'{function_name}_proof_auto.v').resolve()}",
        f"--proof-manual-file={(fresh_dir / f'{function_name}_proof_manual.v').resolve()}",
        f"--coq-logic-path={logic_path}",
        "-slp", str(REPO_ROOT / "annotated") + "/", "SimpleC.EE.CAV",
        f"--input-file={annotated_abs}",
        "--no-exec-info",
    ]
    try:
        proc = subprocess.run(
            cmd,
            cwd=REPO_ROOT / "QualifiedCProgramming",
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout_seconds,
        )
        rc, out, err = proc.returncode, proc.stdout, proc.stderr
    except subprocess.TimeoutExpired:
        rc, out, err = 124, "", f"symexec freshness check timed out after {timeout_seconds}s"
    except OSError as exc:
        rc, out, err = 127, "", f"symexec not runnable: {exc}"

    compared: list[dict[str, str | bool]] = []
    details: list[str] = []
    if rc != 0:
        details.append(f"fresh symexec failed with exit {rc}")
    else:
        for suffix in ("goal", "proof_auto", "goal_check"):
            current = current_dir / f"{function_name}_{suffix}.v"
            fresh = fresh_dir / f"{function_name}_{suffix}.v"
            if not current.exists() or not fresh.exists():
                details.append(f"missing {suffix} artifact for freshness comparison")
                compared.append({"suffix": suffix, "match": False, "current": str(current), "fresh": str(fresh)})
                continue
            current_hash = file_sha256(current)
            fresh_hash = file_sha256(fresh)
            match = current_hash == fresh_hash
            compared.append({
                "suffix": suffix,
                "match": match,
                "current": str(current),
                "fresh": str(fresh),
                "current_sha256": current_hash,
                "fresh_sha256": fresh_hash,
            })
            if not match:
                details.append(f"{suffix} artifact does not match fresh symexec output for current annotated C")

    doc = {
        "annotated_c": str(annotated_abs),
        "annotated_sha256": annotated_hash,
        "symexec_exit": rc,
        "stdout": out,
        "stderr": err,
        "compared": compared,
        "ok": not details,
    }
    log_path.write_text(json.dumps(doc, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    if details:
        return False, f"symexec_freshness_failed:{log_path}"
    return True, f"symexec_freshness_success:{log_path}"


def verify_audit_check(
    *,
    workspace_path: Path,
    function_name: str,
    input_path: Path,
    input_v_path: Path | None,
    annotated_c_path: Path,
) -> tuple[bool, str]:
    checks = [
        verify_proof_artifact_check(workspace_path, function_name, input_v_path),
        source_integrity_gate(
            workspace_path=workspace_path,
            input_path=input_path,
            input_v_path=input_v_path,
            annotated_c_path=annotated_c_path,
        ),
        fingerprint_gate(workspace_path, function_name),
        symexec_freshness_gate(
            workspace_path=workspace_path,
            annotated_c_path=annotated_c_path,
            function_name=function_name,
        ),
    ]
    failures = [detail for ok, detail in checks if not ok]
    if failures:
        return False, ";".join(failures)
    return True, ";".join(detail for _, detail in checks)


def copy_if_exists(src: Path, dst: Path) -> None:
    if not src.exists():
        return
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst)


def export_example_if_needed(workspace_path: Path, function_name: str) -> tuple[bool, str]:
    """On verify success, copy the workspace into experiences/end-end/<name>/.

    Inlined here (the Java pipeline does the same in run_verify); keeps only the
    .v / .c / reasoning artifacts, never the compile intermediates.
    """
    target_dir = EXAMPLES_ROOT / function_name
    if target_dir.exists():
        return False, f"skip_existing:{target_dir}"
    completed, detail = verify_workspace_completed(workspace_path)
    if not completed:
        return False, f"skip_incomplete_verify:{detail}"
    generated_dir = workspace_path / "coq" / "generated"
    if not (generated_dir / f"{function_name}_proof_manual.v").exists():
        return False, f"missing_proof_manual:{generated_dir}/{function_name}_proof_manual.v"

    target_dir.mkdir(parents=True, exist_ok=True)
    original_dir = workspace_path / "original"
    logs_dir = workspace_path / "logs"
    annotated_c = REPO_ROOT / "annotated" / f"{workspace_path.name}.c"

    copy_if_exists(original_dir / f"{function_name}.c", target_dir / "original" / f"{function_name}.c")
    copy_if_exists(original_dir / f"{function_name}.v", target_dir / "original" / f"{function_name}.v")
    copy_if_exists(annotated_c, target_dir / "annotated" / f"{function_name}.c")
    for src in sorted(generated_dir.glob("*.v")):
        copy_if_exists(src, target_dir / "coq" / "generated" / src.name)
    for fname in ("workspace_fingerprint.json", "annotation_reasoning.md", "proof_reasoning.md", "issues.md"):
        copy_if_exists(logs_dir / fname, target_dir / "logs" / fname)

    # Keep only sources: drop any copied compile intermediates and the metrics file.
    coq_runner.clean_compile_artifacts(target_dir)
    metrics = target_dir / "logs" / "metrics.md"
    if metrics.exists():
        metrics.unlink()
    return True, target_dir.as_posix()


def strip_c_comments(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    return re.sub(r"//.*", "", text)


def is_loop_free_candidate(input_path: Path) -> tuple[bool, str]:
    """Conservative gate for deterministic verify without an external agent."""
    text = strip_c_comments(input_path.read_text(encoding="utf-8", errors="replace"))
    forbidden = (r"\bfor\b", r"\bwhile\b", r"\bdo\b", r"\bswitch\b", r"\bgoto\b")
    for pattern in forbidden:
        if re.search(pattern, text):
            return False, f"has_control_flow:{pattern}"
    if not re.search(r"\b\w+(?:\s*\*)?\s+\w+\s*\([^)]*\)\s*\{", text):
        return False, "not_simple_function"
    return True, "loop_free"


def update_trivial_fingerprint(workspace_path: Path, function_name: str, input_path: Path) -> None:
    fingerprint_path = workspace_path / "logs" / "workspace_fingerprint.json"
    data = json.loads(fingerprint_path.read_text(encoding="utf-8"))
    text = strip_c_comments(input_path.read_text(encoding="utf-8", errors="replace"))
    returns = [x.strip() for x in re.findall(r"\breturn\s+([^;]+);", text)]
    returned = ", ".join(f"`{x}`" for x in returns) if returns else "scalar expression(s)"
    pattern = "branch" if re.search(r"\bif\b", text) else "straight_line"
    has_pointer_or_array = "*" in text or "[" in text or "]" in text or "->" in text
    data_shape = "linked_list" if "sll" in input_path.read_text(encoding="utf-8", errors="replace") else ("array" if "[" in text else ("scalar" if not has_pointer_or_array else "pointer"))
    data["semantic_description"] = f"Loop-free function `{function_name}` returning {returned}."
    data["keywords"] = {
        "problem_kind": "math",
        "data": data_shape,
        "pattern": pattern,
    }
    fingerprint_path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def run_symexec(workspace_path: Path, annotated_c_path: Path, function_name: str, timeout_seconds: int = 120) -> tuple[int, str, str]:
    generated_dir = workspace_path / "coq" / "generated"
    generated_dir.mkdir(parents=True, exist_ok=True)
    for old in generated_dir.glob(f"{function_name}_*.v"):
        old.unlink()
    logic_path = f"SimpleC.EE.CAV.{workspace_path.name}"
    cmd = [
        str(REPO_ROOT / "QualifiedCProgramming" / "linux-binary" / "symexec"),
        f"--goal-file={generated_dir / f'{function_name}_goal.v'}",
        f"--proof-auto-file={generated_dir / f'{function_name}_proof_auto.v'}",
        f"--proof-manual-file={generated_dir / f'{function_name}_proof_manual.v'}",
        f"--coq-logic-path={logic_path}",
        "-slp", str(REPO_ROOT / "annotated") + "/", "SimpleC.EE.CAV",
        f"--input-file={annotated_c_path}",
        "--no-exec-info",
    ]
    try:
        proc = subprocess.run(
            cmd,
            cwd=REPO_ROOT / "QualifiedCProgramming",
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout_seconds,
        )
    except subprocess.TimeoutExpired:
        return 124, "", f"symexec timed out after {timeout_seconds}s"
    except OSError as exc:
        return 127, "", f"symexec not runnable: {exc}"
    return proc.returncode, proc.stdout, proc.stderr


def proof_file_has_obligations(proof_file: Path) -> bool:
    if not proof_file.exists():
        return True
    text = proof_file.read_text(encoding="utf-8", errors="replace")
    return bool(re.search(r"\b(Admitted|admit|Abort|Axiom)\b", text))


def proof_manual_has_obligations(generated_dir: Path, function_name: str) -> bool:
    """Verify completion judge: only `proof_manual.v` Admitteds count.

    `proof_auto.v` Admitteds are symexec's normal auto-discharge stubs and are
    accepted by `goal_check.v` as axioms. The agreed completion criterion (memory
    ``proof-auto-admitted-is-normal``): `goal_check.v` compiles and
    `proof_manual.v` contains no `Admitted`/`admit`/`Abort`.
    """
    return proof_file_has_obligations(generated_dir / f"{function_name}_proof_manual.v")


def compile_generated(workspace_path: Path, function_name: str, input_v_path: Path | None, timeout_seconds: int = 120) -> tuple[bool, list[str]]:
    generated_dir = workspace_path / "coq" / "generated"
    original_dir = workspace_path / "original"
    logic_path = f"SimpleC.EE.CAV.{workspace_path.name}"
    extra_q = [(str(original_dir), "")]
    extra_r = [(str(generated_dir), logic_path)]
    logs: list[str] = []

    if input_v_path is not None:
        original_v = original_dir / input_v_path.name
        rc, out, err = coq_runner.run_coqc(original_v, extra_q=extra_q, timeout_seconds=timeout_seconds)
        logs.append(f"$ coqc {original_v}\nrc={rc}\n{out}{err}")
        if rc != 0:
            return False, logs

    for suffix in ("goal", "proof_auto", "proof_manual", "goal_check"):
        path = generated_dir / f"{function_name}_{suffix}.v"
        rc, out, err = coq_runner.run_coqc(path, extra_q=extra_q, extra_r=extra_r, timeout_seconds=timeout_seconds)
        logs.append(f"$ coqc {path}\nrc={rc}\n{out}{err}")
        if rc != 0:
            return False, logs
    return True, logs


def try_trivial_fast_path(
    *,
    workspace_path: Path,
    annotated_c_path: Path,
    input_path: Path,
    input_v_path: Path | None,
    function_name: str,
    model: str,
    reasoning_effort: str,
    export_examples: bool,
    start_iso: str,
    start_wall: float,
) -> tuple[bool, int]:
    if input_v_path is not None:
        return False, 0
    candidate, detail = is_loop_free_candidate(input_path)
    if not candidate:
        emit_log(f"trivial_fast_path_skipped detail={detail}")
        return False, 0

    logs_dir = workspace_path / "logs"
    stdout_log = logs_dir / "deterministic_fast_path_stdout.log"
    stderr_log = logs_dir / "deterministic_fast_path_stderr.log"
    prompt_log = logs_dir / "deterministic_fast_path_prompt.txt"
    last_message = logs_dir / "deterministic_fast_path_last_message.txt"
    prompt_log.write_text("deterministic loop-free fast path; no external agent invoked\n", encoding="utf-8")
    emit_log(f"trivial_fast_path_start detail={detail}")
    update_trivial_fingerprint(workspace_path, function_name, input_path)

    rc, symout, symerr = run_symexec(workspace_path, annotated_c_path, function_name)
    stdout_parts = ["# symexec\n", symout]
    stderr_parts = [symerr]
    generated_dir = workspace_path / "coq" / "generated"
    expected = [generated_dir / f"{function_name}_{suffix}.v" for suffix in ("goal", "proof_auto", "proof_manual", "goal_check")]
    if rc != 0 or not all(path.exists() for path in expected):
        stdout_log.write_text("".join(stdout_parts), encoding="utf-8")
        stderr_log.write_text("".join(stderr_parts), encoding="utf-8")
        emit_log(f"trivial_fast_path_failed stage=symexec rc={rc}")
        return False, 0

    if proof_manual_has_obligations(generated_dir, function_name):
        stdout_log.write_text("".join(stdout_parts), encoding="utf-8")
        stderr_log.write_text("".join(stderr_parts), encoding="utf-8")
        emit_log("trivial_fast_path_failed stage=proof_manual_obligations")
        return False, 0

    ok, compile_logs = compile_generated(workspace_path, function_name, input_v_path)
    stdout_parts.extend(["\n# coqc\n", "\n".join(compile_logs)])
    stdout_log.write_text("".join(stdout_parts), encoding="utf-8")
    stderr_log.write_text("".join(stderr_parts), encoding="utf-8")
    if not ok:
        emit_log("trivial_fast_path_failed stage=coqc")
        return False, 0

    gates_ok, gates_detail = verify_audit_check(
        workspace_path=workspace_path,
        function_name=function_name,
        input_path=input_path,
        input_v_path=input_v_path,
        annotated_c_path=annotated_c_path,
    )
    if not gates_ok:
        emit_log(f"trivial_fast_path_failed stage=audit_check detail={gates_detail}")
        return False, 0

    coq_runner.clean_compile_artifacts(workspace_path / "coq")
    issues = workspace_path / "logs" / "issues.md"
    issues.write_text(
        "# Issues Log\n\n"
        "No issues encountered. Deterministic loop-free fast path completed "
        "symexec and all generated Coq compilation without invoking an external agent.\n",
        encoding="utf-8",
    )
    last_message.write_text(
        "Deterministic loop-free fast path completed successfully.\n",
        encoding="utf-8",
    )
    write_metrics(
        metrics_path(workspace_path),
        status="Success",
        attempts=0,
        last_agent_exit=0,
        start_iso=start_iso,
        end_iso=iso_now(),
        wall_clock_seconds=time.time() - start_wall,
        model=model,
        reasoning_effort=reasoning_effort,
        usage=None,
        prompt_path=prompt_log,
        stdout_jsonl=stdout_log,
        stderr_log=stderr_log,
        last_message_path=last_message,
        input_c=input_path,
        input_v=input_v_path,
        export_examples=export_examples,
    )
    if export_examples:
        exported, export_detail = export_example_if_needed(workspace_path, function_name)
        emit_log(("examples_exported=" if exported else "examples_export_skipped=") + export_detail)
    emit_log("trivial_fast_path_success")
    return True, 0


def bootstrap_workspace(workspace_path: Path, input_path: Path, input_v_path: Path | None, function_name: str) -> Path:
    (workspace_path / "logs").mkdir(parents=True, exist_ok=True)
    (workspace_path / "original").mkdir(parents=True, exist_ok=True)
    (workspace_path / "coq").mkdir(parents=True, exist_ok=True)
    (REPO_ROOT / "annotated").mkdir(parents=True, exist_ok=True)

    original_c = workspace_path / "original" / input_path.name
    annotated_c = REPO_ROOT / "annotated" / f"{workspace_path.name}.c"
    shutil.copy2(input_path, original_c)
    shutil.copy2(input_path, annotated_c)

    original_v = ""
    if input_v_path is not None:
        dst_v = workspace_path / "original" / input_v_path.name
        shutil.copy2(input_v_path, dst_v)
        original_v = str(dst_v)

    fingerprint_path = workspace_path / "logs" / "workspace_fingerprint.json"
    fingerprint = {
        "workspace": workspace_path.name,
        "stage": "verify",
        "input_c": str(input_path),
        "input_v": str(input_v_path) if input_v_path else "",
        "original_c": str(original_c),
        "original_v": original_v,
        "annotated_c": str(annotated_c),
        "function_name": function_name,
        "semantic_description": "",
        "keywords": {},
        "assume_contract_is_correct": True,
        "contract_source": "contract_input_c",
    }
    fingerprint_path.write_text(json.dumps(fingerprint, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return annotated_c


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run Codex externally to execute the full verify workflow.")
    parser.add_argument("input_c", help="Path to input C file, relative to repo root or absolute.")
    parser.add_argument("function_name_positional", nargs="?", help="Optional function name to verify. Kept for CLI compatibility.")
    parser.add_argument("--function-name", help="Function name to verify. Preferred form.")
    parser.add_argument("--skill", default=str(DEFAULT_SKILL), help="Path to verification skill markdown.")
    parser.add_argument("--workspace-name", help="Explicit workspace stem; defaults to input file stem.")
    parser.add_argument("--timestamp", help="Explicit verify timestamp; defaults to current local time.")
    parser.add_argument("--model", default=None, help="Agent model. Defaults to config, else built-in per agent.")
    parser.add_argument(
        "--reasoning-effort",
        default=None,
        help="Agent reasoning effort. Defaults to config, else medium.",
    )
    parser.add_argument("--dry-run", action="store_true", help="Prepare workspace and prompt, but do not invoke Codex.")
    parser.add_argument(
        "--export-examples",
        action="store_true",
        help="If verify succeeds, export the workspace into experiences/end-end/<function_name>/ unless that example already exists.",
    )
    parser.add_argument("--config", default=None, help="Path to agents.json config.")
    parser.add_argument("--agent", choices=["codex", "claude"], default=None)
    parser.add_argument("--codex-bin", default=None, help="Codex CLI binary.")
    parser.add_argument("--claude-bin", default=None, help="Claude CLI binary.")
    parser.add_argument("--timeout-seconds", type=int, default=3600, help="Kill the external agent run if it exceeds this wall-clock timeout.")
    parser.add_argument("--restart-context-file", default=None, help="File whose content (e.g. audit check feedback) is injected into the round-1 prompt on a re-run.")
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()

    cfg = agent_config.load(args.config)
    agent = args.agent or cfg.agent("codex")
    model = args.model or cfg.default_model(agent, DEFAULT_CLAUDE_MODEL if agent == "claude" else DEFAULT_MODEL)
    reasoning_effort = args.reasoning_effort or cfg.reasoning_effort(DEFAULT_REASONING_EFFORT)
    codex_bin = args.codex_bin or cfg.bin("codex", "codex")
    claude_bin = args.claude_bin or cfg.bin("claude", "claude")

    input_path = Path(args.input_c)
    if not input_path.is_absolute():
        input_path = (REPO_ROOT / input_path).resolve()
    skill_path = Path(args.skill)
    if not skill_path.is_absolute():
        skill_path = (REPO_ROOT / skill_path).resolve()

    if not input_path.exists():
        print(f"input file not found: {input_path}", file=sys.stderr)
        return 2
    if input_path.suffix != ".c":
        print(f"input file must be a .c file: {input_path}", file=sys.stderr)
        return 2
    if not skill_path.exists():
        print(f"skill file not found: {skill_path}", file=sys.stderr)
        return 2

    function_name = args.function_name or args.function_name_positional
    if not function_name:
        print("function name is required: pass --function-name NAME or a positional NAME", file=sys.stderr)
        return 2

    input_v_path = paired_input_v(input_path)

    workspace_stem = args.workspace_name or stem_from_input(input_path)
    workspace_timestamp = args.timestamp or timestamp_now()
    workspace_path = OUTPUT_ROOT / f"verify_{workspace_timestamp}_{workspace_stem}"
    annotated_c_path = bootstrap_workspace(workspace_path, input_path, input_v_path, function_name)
    emit_log(f"workspace={workspace_path}")
    emit_log(f"input_c={input_path}")
    emit_log(f"function_name={function_name}")
    emit_log(f"input_v={input_v_path if input_v_path else '<not provided>'}")
    emit_log(f"annotated_c={annotated_c_path}")
    emit_log(f"agent={agent}")
    emit_log(f"model={model}")
    logs_dir = workspace_path / "logs"
    agent_env = build_agent_env(logs_dir)
    reasoning_effort_supported = codex_supports_reasoning_effort(codex_bin, REPO_ROOT, agent_env)
    claude_effort_supported = agent_config.claude_supports_flag(claude_bin, REPO_ROOT, agent_env, "--effort")
    emit_log(f"reasoning_effort={reasoning_effort}")
    emit_log(f"reasoning_effort_supported={reasoning_effort_supported}")
    emit_log(f"claude_effort_supported={claude_effort_supported}")
    run_label = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
    prompt_path = logs_dir / f"agent_prompt_{run_label}.txt"
    stdout_jsonl = logs_dir / f"agent_stdout_{run_label}.jsonl"
    stderr_log = logs_dir / f"agent_stderr_{run_label}.log"
    last_message_path = logs_dir / f"agent_last_message_{run_label}.txt"

    if args.dry_run:
        prompt = build_prompt(skill_path, input_path, input_v_path, function_name, workspace_path, annotated_c_path, 1)
        ensure_parent(prompt_path)
        prompt_path.write_text(prompt, encoding="utf-8")
        write_metrics(
            metrics_path(workspace_path),
            status="Success",
            attempts=0,
            last_agent_exit=0,
            start_iso=iso_now(),
            end_iso=iso_now(),
            wall_clock_seconds=0.0,
            model=model,
            reasoning_effort=reasoning_effort,
            usage=None,
            prompt_path=prompt_path,
            stdout_jsonl=stdout_jsonl,
            stderr_log=stderr_log,
            last_message_path=last_message_path,
            input_c=input_path,
            input_v=input_v_path,
            export_examples=args.export_examples,
        )
        emit_log("dry_run=true")
        print(str(workspace_path))
        return 0

    overall_start_wall = time.time()
    overall_start_iso = iso_now()
    fast_completed, fast_rc = try_trivial_fast_path(
        workspace_path=workspace_path,
        annotated_c_path=annotated_c_path,
        input_path=input_path,
        input_v_path=input_v_path,
        function_name=function_name,
        model=model,
        reasoning_effort=reasoning_effort,
        export_examples=args.export_examples,
        start_iso=overall_start_iso,
        start_wall=overall_start_wall,
    )
    if fast_completed:
        print(str(workspace_path))
        return fast_rc
    proof_only_mode = (
        input_v_path is None
        and is_loop_free_candidate(input_path)[0]
        and (workspace_path / "coq" / "generated" / f"{function_name}_goal.v").exists()
    )
    if proof_only_mode:
        emit_log("agent_mode=proof_only_loop_free")

    total_budget_seconds = args.timeout_seconds
    attempt = 0
    proc_returncode = 1
    completed = False
    usage_total: dict[str, int] | None = None

    verify_restart_context = None
    if args.restart_context_file:
        rc_path = Path(args.restart_context_file)
        if rc_path.exists():
            verify_restart_context = rc_path.read_text(encoding="utf-8", errors="replace")
    if verify_restart_context:
        append_continue(logs_dir, "overturn", verify_restart_context)

    while True:
        attempt += 1
        elapsed_before = time.time() - overall_start_wall
        remaining_budget = total_budget_seconds - elapsed_before
        if remaining_budget <= 0:
            emit_log("agent_exec_budget_exhausted")
            proc_returncode = 124
            break

        run_label = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
        prompt_path = logs_dir / f"agent_prompt_{run_label}.txt"
        stdout_jsonl = logs_dir / f"agent_stdout_{run_label}.jsonl"
        stderr_log = logs_dir / f"agent_stderr_{run_label}.log"
        last_message_path = logs_dir / f"agent_last_message_{run_label}.txt"
        retry_context = verify_restart_context
        continue_path = logs_dir / "continue.md"
        if continue_path.exists():
            retry_context = continue_path.read_text(encoding="utf-8", errors="replace")
        if proof_only_mode:
            prompt = build_proof_only_prompt(
                skill_path,
                input_path,
                input_v_path,
                function_name,
                workspace_path,
                annotated_c_path,
                attempt,
                retry_context,
            )
        else:
            prompt = build_prompt(
                skill_path,
                input_path,
                input_v_path,
                function_name,
                workspace_path,
                annotated_c_path,
                attempt,
                retry_context,
            )
        ensure_parent(prompt_path)
        prompt_path.write_text(prompt, encoding="utf-8")

        round_timeout = max(1, int(remaining_budget))
        cmd = [
            args.codex_bin,
            "--dangerously-bypass-approvals-and-sandbox",
            "exec",
            "--json",
            "--skip-git-repo-check",
            "-C",
            str(REPO_ROOT),
            "-o",
            str(last_message_path),
        ]
        emit_log(
            f"agent_exec_start attempt={attempt} round_timeout_seconds={round_timeout} total_budget_seconds={total_budget_seconds}"
        )

        start_wall = time.time()
        start_iso = iso_now()
        failure_detail = None
        try:
            if agent == "claude":
                cmd = [
                    claude_bin,
                    "--print",
                    "--dangerously-skip-permissions",
                    "--add-dir",
                    str(REPO_ROOT),
                    "--output-format",
                    "stream-json",
                    "--verbose",
                ]
                if model:
                    cmd.extend(["--model", model])
                if reasoning_effort and claude_effort_supported:
                    cmd.extend(["--effort", reasoning_effort])
                with stdout_jsonl.open("w", encoding="utf-8") as out_f, stderr_log.open("w", encoding="utf-8") as err_f:
                    proc = subprocess.run(
                        cmd,
                        input=prompt,
                        text=True,
                        stdout=out_f,
                        stderr=err_f,
                        cwd=REPO_ROOT,
                        timeout=round_timeout,
                        env=agent_env,
                    )
                proc_returncode = proc.returncode
                last_message = agent_metrics.extract_claude_last_message(stdout_jsonl)
                if last_message is not None:
                    last_message_path.write_text(last_message, encoding="utf-8")
                elif stdout_jsonl.exists():
                    last_message_path.write_text(stdout_jsonl.read_text(encoding="utf-8", errors="replace"), encoding="utf-8")
            else:
                cmd = [
                    codex_bin,
                    "--dangerously-bypass-approvals-and-sandbox",
                    "exec",
                    "--json",
                    "--skip-git-repo-check",
                    "-C",
                    str(REPO_ROOT),
                    "-o",
                    str(last_message_path),
                ]
                if model:
                    cmd.extend(["--model", model])
                if reasoning_effort and reasoning_effort_supported:
                    cmd.extend(["--reasoning-effort", reasoning_effort])
                cmd.append("-")
                with stdout_jsonl.open("w", encoding="utf-8") as out_f, stderr_log.open("w", encoding="utf-8") as err_f:
                    proc = subprocess.run(
                        cmd,
                        input=prompt,
                        text=True,
                        stdout=out_f,
                        stderr=err_f,
                        cwd=REPO_ROOT,
                        timeout=round_timeout,
                        env=agent_env,
                    )
                proc_returncode = proc.returncode
        except subprocess.TimeoutExpired:
            proc_returncode = 124
            failure_detail = f"external agent run exceeded remaining timeout budget of {round_timeout} seconds"
            emit_log(f"agent_exec_timeout attempt={attempt} detail={failure_detail}")
        end_wall = time.time()
        filter_stderr_in_place(stderr_log)

        usage_total = agent_metrics.add_usage(usage_total, agent_metrics.parse_usage(agent, stdout_jsonl))

        if proc_returncode != 0:
            update_issues_on_failure(
                workspace_path / "logs" / "issues.md",
                "external-agent-run",
                proc_returncode,
                stderr_log,
            )
            if failure_detail is not None:
                issues_path = workspace_path / "logs" / "issues.md"
                existing = issues_path.read_text(encoding="utf-8").rstrip() + "\n"
                issues_path.write_text(existing + f"- Detail: `{failure_detail}`\n", encoding="utf-8")
            emit_log(f"agent_exec_failed attempt={attempt} exit_code={proc_returncode}")
        else:
            emit_log(f"agent_exec_completed attempt={attempt} exit_code=0")

        completed, detail = verify_audit_check(
            workspace_path=workspace_path,
            function_name=function_name,
            input_path=input_path,
            input_v_path=input_v_path,
            annotated_c_path=annotated_c_path,
        )
        if completed:
            emit_log(f"verify_completed={detail}")
            if args.export_examples:
                exported, export_detail = export_example_if_needed(workspace_path, function_name)
                if exported:
                    emit_log(f"examples_exported={export_detail}")
                else:
                    emit_log(f"examples_export_skipped={export_detail}")
            proc_returncode = 0
            break

        elapsed_total = time.time() - overall_start_wall
        if elapsed_total >= total_budget_seconds:
            emit_log("agent_exec_budget_exhausted_after_attempt")
            if proc_returncode == 0:
                proc_returncode = 124
            break

        emit_log(
            f"verify_incomplete_retrying attempt={attempt} detail={detail} remaining_seconds={max(0, int(total_budget_seconds - elapsed_total))}"
        )
        append_continue(
            logs_dir,
            f"retry-after-attempt-{attempt}",
            verify_retry_feedback(attempt, detail, workspace_path, function_name),
        )

    # experiences/general/COMPILE/README.md §10: drop coqc intermediates (.vo/.glob/.aux) from the
    # workspace coq dirs, keeping .v sources. Never touches the shared QCP tree.
    removed = coq_runner.clean_compile_artifacts(workspace_path / "coq")
    emit_log(f"cleaned_compile_artifacts count={len(removed)}")

    overall_end_iso = iso_now()
    write_metrics(
        metrics_path(workspace_path),
        status="Success" if proc_returncode == 0 else "Fail",
        attempts=attempt,
        last_agent_exit=proc_returncode,
        start_iso=overall_start_iso,
        end_iso=overall_end_iso,
        wall_clock_seconds=time.time() - overall_start_wall,
        model=model,
        reasoning_effort=reasoning_effort,
        usage=usage_total,
        prompt_path=prompt_path,
        stdout_jsonl=stdout_jsonl,
        stderr_log=stderr_log,
        last_message_path=last_message_path,
        input_c=input_path,
        input_v=input_v_path,
        export_examples=args.export_examples,
    )

    emit_log(f"stdout_jsonl={stdout_jsonl}")
    emit_log(f"stderr_log={stderr_log}")
    emit_log(f"last_message={last_message_path}")

    print(str(workspace_path))
    return proc_returncode


def metrics_path(workspace_path: Path) -> Path:
    return workspace_path / "logs" / "metrics.md"


if __name__ == "__main__":
    sys.exit(main())

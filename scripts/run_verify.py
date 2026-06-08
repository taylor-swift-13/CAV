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
import threading
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import agent_config
import agent_metrics
import check_qcp_cheating


REPO_ROOT = Path(__file__).resolve().parents[1]
import coq_runner

QCP_ROOT = REPO_ROOT / "QualifiedCProgramming"
QCP_SL_DIR = QCP_ROOT / "SeparationLogic"
QCP_CAV_INPUT_ROOT = QCP_ROOT / "QCP_examples" / "CAV"
QCP_CAV_EXAMPLES_ROOT = QCP_SL_DIR / "examples" / "CAV"
QCP_CAV_ORIGINAL_ROOT = QCP_SL_DIR / "_cav_original"
QCP_CAV_LOCK_ROOT = QCP_SL_DIR / "_cav_locks"

DEFAULT_SKILL = REPO_ROOT / "skills" / "verify" / "SKILL.md"
OUTPUT_ROOT = REPO_ROOT / "output"
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


def iso_from_epoch(epoch: float) -> str:
    return dt.datetime.fromtimestamp(epoch).astimezone().strftime("%Y-%m-%d %H:%M:%S.%f %z")


def _tsv_cell(value: object) -> str:
    return str(value if value is not None else "").replace("\t", " ").replace("\n", " ").replace("\r", " ")


def _timeline_row(epoch: float, line_no: int, raw_line: str) -> str:
    event_type = ""
    item_type = ""
    item_status = ""
    item_id = ""
    command = ""
    try:
        obj = json.loads(raw_line)
    except json.JSONDecodeError:
        obj = {}
    if isinstance(obj, dict):
        event_type = obj.get("type") or ""
        item = obj.get("item")
        if isinstance(item, dict):
            item_type = item.get("type") or ""
            item_status = item.get("status") or ""
            item_id = item.get("id") or ""
            command = item.get("command") or ""
    return "\t".join(
        _tsv_cell(v)
        for v in (
            f"{epoch:.6f}",
            iso_from_epoch(epoch),
            line_no,
            event_type,
            item_type,
            item_status,
            item_id,
            command,
        )
    )


def run_agent_with_timeline(
    cmd: list[str],
    *,
    prompt: str,
    stdout_jsonl: Path,
    stdout_timeline: Path,
    stderr_log: Path,
    cwd: Path,
    timeout: int,
    env: dict[str, str],
) -> int:
    ensure_parent(stdout_jsonl)
    stdout_timeline.parent.mkdir(parents=True, exist_ok=True)
    with stdout_jsonl.open("w", encoding="utf-8") as out_f, \
            stdout_timeline.open("w", encoding="utf-8") as timeline_f, \
            stderr_log.open("w", encoding="utf-8") as err_f:
        timeline_f.write("epoch\tiso_time\tline_no\tevent_type\titem_type\titem_status\titem_id\tcommand\n")
        proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=err_f,
            text=True,
            cwd=cwd,
            env=env,
            bufsize=1,
        )
        writer_error: list[BaseException] = []

        def write_prompt() -> None:
            try:
                assert proc.stdin is not None
                proc.stdin.write(prompt)
                proc.stdin.close()
            except BaseException as exc:
                writer_error.append(exc)

        def read_stdout() -> None:
            assert proc.stdout is not None
            line_no = 0
            for line in proc.stdout:
                line_no += 1
                epoch = time.time()
                out_f.write(line)
                out_f.flush()
                timeline_f.write(_timeline_row(epoch, line_no, line) + "\n")
                timeline_f.flush()

        writer = threading.Thread(target=write_prompt, daemon=True)
        reader = threading.Thread(target=read_stdout, daemon=True)
        writer.start()
        reader.start()
        try:
            returncode = proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait()
            reader.join(timeout=5)
            writer.join(timeout=5)
            raise
        reader.join(timeout=5)
        writer.join(timeout=5)
        return returncode


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


def imported_coq_dependency_paths(input_path: Path) -> list[Path]:
    text = input_path.read_text(encoding="utf-8", errors="replace")
    modules = sorted(set(re.findall(r"Import\s+Coq\s+Require\s+Import\s+([A-Za-z0-9_]+)", text)))
    deps: list[Path] = []
    for module in modules:
        candidate = input_path.parent / f"{module}.v"
        if candidate.exists():
            deps.append(candidate)
    return deps


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
        "Persistence requirement: do not finish this agent run merely because a repairable gate failed. If symexec/coqc/proof/manual-obligation feedback points to a concrete annotation or proof edit inside this workspace, keep editing and rerunning the relevant gate until success, a genuinely unrepairable contract/input blocker is found, or the external timeout stops you. A single new blocker is work to continue, not a reason to write Final Result: Fail.",
        "",
        "Compile boundary: follow QCP's official .agents final-check instructions for symexec/coqc/coqtop. The CAV path adaptation is only that the current case is staged in the current workspace's QCP mirror under QualifiedCProgramming, and output/ remains the workspace/artifact directory. Do not invent a separate output/coq/generated compile method, do not parallelize a dependency-ordered QCP final-check sequence, and never copy .vo/.glob/.aux files back to output. The runner repeats the same QCP final-check audit and collects only final .v artifacts at the end.",
        "",
        "Repository write boundary: edit only this verify workspace, the active annotated C file, generated proof_manual.v for this target, and the current workspace's QCP mirror directories for compilation. Do not edit skills/, scripts/, QCP source files, unrelated QCP examples, or unrelated inputs.",
        "",
        "Read boundary: do not read any other output workspace or any other QCP mirror workspace under QualifiedCProgramming/QCP_examples/CAV, QualifiedCProgramming/SeparationLogic/examples/CAV, or QualifiedCProgramming/SeparationLogic/_cav_original. Only the current workspace and the current workspace's mirror are in scope.",
        "",
        "Symexec rerun rule: before any symexec rerun, the previous coq/generated files must be preserved under coq/last for reference. The runner's run_symexec helper does this automatically. After symexec regenerates proof_manual.v, consult coq/last/*_proof_manual.v and reuse the prior proof structure manually; if an old witness statement and the new witness statement are exactly identical, copy that proof verbatim from coq/last. Do not expect proofs to be spliced automatically and do not rewrite from scratch when coq/last has useful proof text.",
        "",
        "Inputs:",
        _input_lines(input_path, input_v_path, function_name, workspace_path, annotated_c_path).rstrip(),
    ]
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
        "Persistence requirement: proof-only mode must keep proving while proof_manual.v can still be edited. Do not exit just because proof_manual_has_obligations remains, one theorem fails under QCP-mirror coqc, or a tactic needs adjustment; continue the edit/QCP-compile loop until proof_manual.v has no placeholders and QCP-mirror goal_check.v compiles, or until you identify a genuinely unprovable VC under the current contract.",
        "",
        "Compile boundary: follow QCP's official .agents final-check instructions for symexec/coqc/coqtop. The CAV path adaptation is only that the current case is staged in the current workspace's QCP mirror under QualifiedCProgramming, and output/ remains the workspace/artifact directory. Do not invent a separate output/coq/generated compile method, do not parallelize a dependency-ordered QCP final-check sequence, and never copy .vo/.glob/.aux files back to output. The runner repeats the same QCP final-check audit and collects only final .v artifacts at the end.",
        "",
        "Repository write boundary: edit only this verify workspace, the active annotated C file, generated proof_manual.v for this target, and the current workspace's QCP mirror directories for compilation. Do not edit skills/, scripts/, QCP source files, unrelated QCP examples, or unrelated inputs.",
        "",
        "Read boundary: do not read any other output workspace or any other QCP mirror workspace under QualifiedCProgramming/QCP_examples/CAV, QualifiedCProgramming/SeparationLogic/examples/CAV, or QualifiedCProgramming/SeparationLogic/_cav_original. Only the current workspace and the current workspace's mirror are in scope.",
        "",
        "Do not rerun symexec in proof-only mode. If a prior generated snapshot exists under coq/last, it is read-only reference material for proof structure.",
        "",
        "Mode: proof-only (also follow MODE_PROOF_ONLY.md per SKILL.md §4.5c).",
        "",
        "Inputs:",
        _input_lines(input_path, input_v_path, function_name, workspace_path, annotated_c_path).rstrip(),
    ]
    if restart_context:
        lines += ["", "Restart feedback (must be addressed before finishing this verify run):", restart_context.rstrip()]
    return "\n".join(lines) + "\n"


def _phase_log(workspace_path: Path, event: str, detail: str = "") -> None:
    """Append a timestamped phase event to <ws>/logs/phase_timeline.tsv (best-effort).
    Initial symexec and agent-triggered reruns share this timeline."""
    try:
        import time as _t
        p = workspace_path / "logs" / "phase_timeline.tsv"
        p.parent.mkdir(parents=True, exist_ok=True)
        with open(p, "a", encoding="utf-8") as f:
            f.write(f"{_t.time():.3f}\t{_t.strftime('%Y-%m-%d %H:%M:%S')}\t{event}\t{detail}\n")
    except Exception:
        pass


def phase_timing_lines(metrics_md_path: Path, start_iso: str, end_iso: str, stdout_timeline: Path | None = None) -> list[str]:
    """Aggregate phase_timeline.tsv into per annotation↔proof cycle durations.
    Each symexec run bounds a cycle; the gap to the next symexec (or run end) is the
    time spent proving/editing against that annotation version."""
    import datetime
    tl = metrics_md_path.parent / "phase_timeline.tsv"
    if not tl.exists():
        return []
    def _ep(iso: str):
        for parser in (
            lambda s: datetime.datetime.strptime(s, "%Y-%m-%d %H:%M:%S %z"),
            datetime.datetime.fromisoformat,
        ):
            try:
                return parser(iso).timestamp()
            except Exception:
                continue
        return None
    starts: list[float] = []
    dones: list[float] = []
    last_ep = None
    for ln in tl.read_text(encoding="utf-8", errors="replace").splitlines():
        p = ln.split("\t")
        if len(p) < 3:
            continue
        try:
            ep = float(p[0])
        except ValueError:
            continue
        last_ep = ep
        if p[2] in ("symexec_init_start", "symexec_rerun_start"):
            starts.append(ep)
        elif p[2] in ("symexec_init_done", "symexec_rerun_done"):
            dones.append(ep)
    if not starts:
        return []
    coqc_done: list[float] = []
    if stdout_timeline and stdout_timeline.exists():
        for ln in stdout_timeline.read_text(encoding="utf-8", errors="replace").splitlines()[1:]:
            p = ln.split("\t")
            if len(p) < 8:
                continue
            try:
                ep = float(p[0])
            except ValueError:
                continue
            event_type, item_type, item_status, command = p[3], p[4], p[5], p[7]
            if event_type == "item.completed" and item_type == "command_execution" and item_status == "completed":
                if re.search(r"(^|[/\s'\"])(coqc|coqtop)(\s|$)", command):
                    coqc_done.append(ep)
    run_start, run_end = _ep(start_iso), (_ep(end_iso) or last_ep)
    out = [f"- Annotation↔proof cycles (symexec runs): `{len(starts)}`"]
    if run_start and run_end:
        annotation_seconds = 0.0
        prev_symexec = run_start
        for s in starts:
            coqc_since_prev_symexec = [c for c in coqc_done if prev_symexec <= c <= s]
            if coqc_since_prev_symexec:
                annotation_seconds += max(0.0, s - max(coqc_since_prev_symexec))
            else:
                annotation_seconds += max(0.0, s - prev_symexec)
            prev_symexec = s
        total_seconds = max(0.0, run_end - run_start)
        proof_seconds = max(0.0, total_seconds - annotation_seconds)
        out.append(f"- Annotation phase time (estimated seconds): `{annotation_seconds:.1f}`")
        out.append(f"- Proof phase time (estimated seconds): `{proof_seconds:.1f}`")
    if run_start:
        out.append(f"  - initial annotation (run start → 1st symexec): `{starts[0]-run_start:.1f}s`")
    for i, s in enumerate(starts):
        nxt = starts[i + 1] if i + 1 < len(starts) else (run_end or s)
        out.append(f"  - cycle {i+1}: symexec, then `{max(0.0, nxt - s):.1f}s` proving/edit before next")
    return out


def write_metrics(
    metrics_md_path: Path,
    *,
    status: str,
    attempts: int,
    last_agent_exit: int,
    start_iso: str,
    end_iso: str,
    wall_clock_seconds: float,
    agent: str,
    model: str,
    reasoning_effort: str,
    usage: dict[str, int] | None,
    prompt_path: Path,
    stdout_jsonl: Path,
    stdout_timeline: Path | None = None,
    stderr_log: Path,
    last_message_path: Path,
    input_c: Path,
    input_v: Path | None,
    annotated_snapshot: Path | None = None,
    annotated_cleanup: str = "not attempted",
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
        f"- Agent: `{agent}`",
        f"- Model: `{model or 'n/a'}`",
        f"- Reasoning effort: `{reasoning_effort or 'n/a'}`",
        f"- Input C: `{input_c}`",
        f"- Input V: `{input_v if input_v else '<not provided>'}`",
        f"- Annotated C snapshot: `{annotated_snapshot if annotated_snapshot else '<not saved>'}`",
        f"- Annotated C global cleanup: `{annotated_cleanup}`",
        f"- Prompt file: `{prompt_path}`",
        f"- Agent stdout: `{stdout_jsonl}`",
        f"- Agent stdout timeline: `{stdout_timeline if stdout_timeline else '<not recorded>'}`",
        f"- Agent stderr: `{stderr_log}`",
        f"- Agent last message: `{last_message_path}`",
    ]
    lines.extend(agent_metrics.usage_lines(
        usage, prompt_path=prompt_path, last_message_path=last_message_path))
    lines.extend(phase_timing_lines(metrics_md_path, start_iso, end_iso, stdout_timeline))
    lines.extend(["- Experience updates: none", f"Final Result: {status}"])
    metrics_md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def save_annotated_snapshot(workspace_path: Path, annotated_c_path: Path) -> Path | None:
    if not annotated_c_path.exists():
        return None
    snapshot = workspace_path / "annotated" / annotated_c_path.name
    snapshot.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(annotated_c_path, snapshot)
    return snapshot


def cleanup_global_annotated_after_snapshot(annotated_c_path: Path, annotated_snapshot: Path | None) -> str:
    """Remove the repo-level annotated file after preserving it in the workspace."""
    if annotated_snapshot is None or not annotated_snapshot.exists():
        return "skipped: snapshot missing"
    if not annotated_c_path.exists():
        return "already absent"
    try:
        annotated_c_path.unlink()
    except OSError as exc:
        return f"failed: {exc}"
    return f"deleted {annotated_c_path}"


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


def verify_workspace_final_result(workspace_path: Path) -> str:
    """Return the agent-declared final result state from metrics.md."""
    _, detail = verify_workspace_completed(workspace_path)
    return detail


def verify_proof_artifact_check(
    workspace_path: Path,
    function_name: str,
    input_v_path: Path | None,
    annotated_c_path: Path,
    input_path: Path,
) -> tuple[bool, str]:
    generated_dir = workspace_path / "coq" / "generated"
    manual_path = generated_dir / f"{function_name}_proof_manual.v"
    if not manual_path.exists():
        missing = [str(manual_path)]
    else:
        missing = []
    if missing:
        return False, "missing_generated_files:" + ",".join(missing)

    if proof_manual_has_obligations(generated_dir, function_name):
        return False, f"proof_manual_has_obligations:{manual_path}"

    ok, compile_logs = compile_generated_via_qcp_mirror(
        workspace_path,
        function_name,
        input_path,
        input_v_path,
        annotated_c_path,
    )
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


def verify_audit_check(
    *,
    workspace_path: Path,
    function_name: str,
    input_path: Path,
    input_v_path: Path | None,
    annotated_c_path: Path,
) -> tuple[bool, str]:
    checks = [
        source_integrity_gate(
            workspace_path=workspace_path,
            input_path=input_path,
            input_v_path=input_v_path,
            annotated_c_path=annotated_c_path,
        ),
        verify_proof_artifact_check(workspace_path, function_name, input_v_path, annotated_c_path, input_path),
    ]
    failures = [detail for ok, detail in checks if not ok]
    if failures:
        return False, ";".join(failures)
    return True, ";".join(detail for _, detail in checks)


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


def snapshot_generated_for_reference(workspace_path: Path, function_name: str) -> Path | None:
    generated_dir = workspace_path / "coq" / "generated"
    if not generated_dir.exists() or not any(generated_dir.glob(f"{function_name}_*.v")):
        return None
    last_dir = workspace_path / "coq" / "last"
    if last_dir.exists():
        shutil.rmtree(last_dir)
    shutil.copytree(generated_dir, last_dir)
    return last_dir


def run_symexec(
    workspace_path: Path,
    annotated_c_path: Path,
    function_name: str,
    timeout_seconds: int = 120,
    *,
    preserve_manual: bool = False,
) -> tuple[int, str, str]:
    generated_dir = workspace_path / "coq" / "generated"
    generated_dir.mkdir(parents=True, exist_ok=True)
    _phase_log(workspace_path, "symexec_init_start")
    last_dir = snapshot_generated_for_reference(workspace_path, function_name)
    if last_dir is not None:
        _phase_log(workspace_path, "symexec_previous_generated_snapshot", str(last_dir))
    suffixes_to_refresh = ("goal", "proof_auto", "goal_check") if preserve_manual else ("goal", "proof_auto", "proof_manual", "goal_check")
    for suffix in suffixes_to_refresh:
        old = generated_dir / f"{function_name}_{suffix}.v"
        if old.exists():
            old.unlink()
    logic_path = f"SimpleC.EE.CAV.{workspace_path.name}"
    cmd = [
        str(REPO_ROOT / "QualifiedCProgramming" / "linux-binary" / "symexec"),
        f"--goal-file={generated_dir / f'{function_name}_goal.v'}",
        f"--proof-auto-file={generated_dir / f'{function_name}_proof_auto.v'}",
        f"--proof-manual-file={generated_dir / f'{function_name}_proof_manual.v'}",
        f"--coq-logic-path={logic_path}",
        # Strategy lib path = canonical QCP_demos_LLM strategies, qualified to
        # SimpleC.EE.QCP_demos_LLM so generated goal.v emits prefixed requires
        # (`From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal`),
        # which resolve uniquely even with duplicate demo dirs on the load-path.
        # humaneval cases reuse the generic, pre-built int/char-array strategies.
        "-slp", str(REPO_ROOT / "QualifiedCProgramming" / "QCP_examples" / "QCP_demos_LLM") + "/", "SimpleC.EE.QCP_demos_LLM",
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


BARE_REQUIRE_IMPORT_RE = re.compile(r"^\s*Require\s+Import\s+([A-Za-z0-9_]+)\s*\.", re.M)
FROM_BARE_REQUIRE_IMPORT_RE = re.compile(r"^\s*From\s+([A-Za-z0-9_]+)\s+Require\s+Import\s+([A-Za-z0-9_ ]+)\s*\.", re.M)


def _copy_tree_v_files(source_dir: Path, target_dir: Path) -> list[str]:
    target_dir.mkdir(parents=True, exist_ok=True)
    copied: list[str] = []
    for source in sorted(source_dir.glob("*.v")):
        target = target_dir / source.name
        shutil.copy2(source, target)
        copied.append(f"staged original v dep: {target} <- {source}")
    return copied


def _copy_header_deps(source_dir: Path, target_dir: Path) -> list[str]:
    target_dir.mkdir(parents=True, exist_ok=True)
    copied: list[str] = []
    for header in ("verification_stdlib.h", "verification_list.h", "int_array_def.h", "long_array_def.h", "char_array_def.h"):
        source = REPO_ROOT / header
        if source.exists():
            shutil.copy2(source, target_dir / header)
            copied.append(f"staged root header: {target_dir / header} <- {source}")
    for source in sorted(source_dir.glob("*.h")):
        target = target_dir / source.name
        shutil.copy2(source, target)
        copied.append(f"staged input header: {target} <- {source}")
    return copied


def local_coq_dependency_order(root_v: Path, staged_dir: Path) -> list[Path]:
    """Return local staged Coq files needed for root_v, deps before users."""
    order: list[Path] = []
    visiting: set[str] = set()
    done: set[str] = set()

    def visit(module: str) -> None:
        if module in done or module in visiting:
            return
        path = staged_dir / f"{module}.v"
        if not path.exists():
            return
        visiting.add(module)
        text = path.read_text(encoding="utf-8", errors="replace")
        for dep in BARE_REQUIRE_IMPORT_RE.findall(text):
            if (staged_dir / f"{dep}.v").exists():
                visit(dep)
        for prefix, imports in FROM_BARE_REQUIRE_IMPORT_RE.findall(text):
            if prefix == "Coq":
                continue
            for dep in imports.split():
                candidate = f"{prefix}_{dep}"
                if (staged_dir / f"{candidate}.v").exists():
                    visit(candidate)
        visiting.remove(module)
        done.add(module)
        order.append(path)

    visit(root_v.stem)
    return order


def canonicalize_manual_goal_import(manual_path: Path, function_name: str, logic_path: str) -> None:
    text = manual_path.read_text(encoding="utf-8", errors="replace")
    pattern = re.compile(
        rf"^\s*From\s+SimpleC\.EE(?:\.[A-Za-z0-9_]+)*\s+Require\s+Import\s+{re.escape(function_name)}_goal\s*\.",
        re.M,
    )
    replacement = f"From {logic_path} Require Import {function_name}_goal."
    new_text, count = pattern.subn(replacement, text)
    if count == 0:
        bare_pattern = re.compile(rf"^\s*Require\s+Import\s+{re.escape(function_name)}_goal\s*\.", re.M)
        new_text = bare_pattern.sub(replacement, text)
    if new_text != text:
        manual_path.write_text(new_text, encoding="utf-8")


def acquire_qcp_mirror_lock(workspace_name: str, timeout_seconds: int) -> Path:
    QCP_CAV_LOCK_ROOT.mkdir(parents=True, exist_ok=True)
    lock_dir = QCP_CAV_LOCK_ROOT / workspace_name
    deadline = time.time() + max(1, timeout_seconds)
    while True:
        try:
            lock_dir.mkdir()
            (lock_dir / "pid").write_text(str(os.getpid()) + "\n", encoding="utf-8")
            return lock_dir
        except FileExistsError:
            if time.time() >= deadline:
                raise TimeoutError(f"timed out waiting for QCP mirror lock: {lock_dir}")
            time.sleep(0.2)


def compile_generated_via_qcp_mirror(
    workspace_path: Path,
    function_name: str,
    input_path: Path,
    input_v_path: Path | None,
    annotated_c_path: Path,
    timeout_seconds: int = 120,
) -> tuple[bool, list[str]]:
    """Run the official Coq chain from a QCP examples mirror.

    The generated Coq files are placed under
    ``SeparationLogic/examples/CAV/<workspace>`` and compiled with QCP's normal
    ``-R examples SimpleC.EE`` load-path. Original problem specs and sibling
    HumanEval support files are staged under a separate bare namespace via
    ``-Q _cav_original/<workspace> ""`` because many input specs use bare
    imports such as ``Require Import string_bridge``.
    """
    workspace_name = workspace_path.name
    qcp_input_dir = QCP_CAV_INPUT_ROOT / workspace_name
    qcp_examples_dir = QCP_CAV_EXAMPLES_ROOT / workspace_name
    qcp_original_dir = QCP_CAV_ORIGINAL_ROOT / workspace_name
    generated_dir = workspace_path / "coq" / "generated"
    manual_path = generated_dir / f"{function_name}_proof_manual.v"
    logs: list[str] = []
    lock_dir: Path | None = None

    try:
        try:
            lock_dir = acquire_qcp_mirror_lock(workspace_name, timeout_seconds)
            logs.append(f"acquired QCP mirror lock: {lock_dir}")
        except TimeoutError as exc:
            logs.append(str(exc))
            return False, logs

        for directory in (qcp_input_dir, qcp_examples_dir, qcp_original_dir):
            if directory.exists():
                shutil.rmtree(directory)
            directory.mkdir(parents=True, exist_ok=True)

        qcp_annotated = qcp_input_dir / annotated_c_path.name
        shutil.copy2(annotated_c_path, qcp_annotated)
        logs.append(f"staged annotated C: {qcp_annotated} <- {annotated_c_path}")
        logs.extend(_copy_header_deps(input_path.parent, qcp_input_dir))
        if input_v_path is not None:
            logs.extend(_copy_tree_v_files(input_v_path.parent, qcp_original_dir))
        logic_path = f"SimpleC.EE.CAV.{workspace_name}"
        qcp_manual_path = qcp_examples_dir / manual_path.name
        shutil.copy2(manual_path, qcp_manual_path)
        canonicalize_manual_goal_import(qcp_manual_path, function_name, logic_path)
        logs.append(f"staged proof_manual: {qcp_manual_path} <- {manual_path}")

        sym_cmd = [
            str(QCP_ROOT / "linux-binary" / "symexec"),
            f"--goal-file=SeparationLogic/examples/CAV/{workspace_name}/{function_name}_goal.v",
            f"--proof-auto-file=SeparationLogic/examples/CAV/{workspace_name}/{function_name}_proof_auto.v",
            f"--proof-manual-file=SeparationLogic/examples/CAV/{workspace_name}/{function_name}_proof_manual.v",
            f"--coq-logic-path={logic_path}",
            "-slp", "QCP_examples/QCP_demos_LLM/", "SimpleC.EE.QCP_demos_LLM",
            f"--input-file=QCP_examples/CAV/{workspace_name}/{qcp_annotated.name}",
            "--no-exec-info",
        ]
        try:
            proc = subprocess.run(
                sym_cmd,
                cwd=QCP_ROOT,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=timeout_seconds,
            )
            logs.append("$ " + " ".join(sym_cmd) + f"\nrc={proc.returncode}\n{proc.stdout}{proc.stderr}")
        except subprocess.TimeoutExpired:
            logs.append("$ " + " ".join(sym_cmd) + f"\nrc=124\nsymexec timed out after {timeout_seconds}s")
            return False, logs
        except OSError as exc:
            logs.append("$ " + " ".join(sym_cmd) + f"\nrc=127\nsymexec not runnable: {exc}")
            return False, logs
        if proc.returncode != 0:
            return False, logs

        extra_q = [(str(qcp_original_dir), "")]
        coq_files: list[Path] = []
        if input_v_path is not None:
            coq_files.extend(local_coq_dependency_order(qcp_original_dir / input_v_path.name, qcp_original_dir))
        coq_files.extend(qcp_examples_dir / f"{function_name}_{suffix}.v" for suffix in ("goal", "proof_auto", "proof_manual", "goal_check"))
        for path in coq_files:
            rc, out, err = coq_runner.run_coqc(path, extra_q=extra_q, timeout_seconds=timeout_seconds)
            logs.append(f"$ coqc {path}\nrc={rc}\n{out}{err}")
            if rc != 0:
                return False, logs

        generated_dir.mkdir(parents=True, exist_ok=True)
        for suffix in ("goal", "proof_auto", "proof_manual", "goal_check"):
            source = qcp_examples_dir / f"{function_name}_{suffix}.v"
            target = generated_dir / source.name
            shutil.copy2(source, target)
            logs.append(f"collected final QCP artifact: {target} <- {source}")
        return True, logs
    finally:
        coq_runner.clean_compile_artifacts(qcp_examples_dir, recursive=False)
        coq_runner.clean_compile_artifacts(qcp_original_dir, recursive=False)
        if qcp_input_dir.exists():
            shutil.rmtree(qcp_input_dir)
        if qcp_examples_dir.exists():
            shutil.rmtree(qcp_examples_dir)
        if qcp_original_dir.exists():
            shutil.rmtree(qcp_original_dir)
        if lock_dir is not None and lock_dir.exists():
            shutil.rmtree(lock_dir)


def try_trivial_fast_path(
    *,
    workspace_path: Path,
    annotated_c_path: Path,
    input_path: Path,
    input_v_path: Path | None,
    function_name: str,
    model: str,
    reasoning_effort: str,
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

    stdout_parts.append(
        "\n# audit\n"
        "Skipping pre-audit coqc replay; verify_audit_check owns the single "
        "authoritative compile pass for this deterministic fast path.\n"
    )
    stdout_log.write_text("".join(stdout_parts), encoding="utf-8")
    stderr_log.write_text("".join(stderr_parts), encoding="utf-8")

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
    annotated_snapshot = save_annotated_snapshot(workspace_path, annotated_c_path)
    annotated_cleanup = cleanup_global_annotated_after_snapshot(annotated_c_path, annotated_snapshot)
    write_metrics(
        metrics_path(workspace_path),
        status="Success",
        attempts=0,
        last_agent_exit=0,
        start_iso=start_iso,
        end_iso=iso_now(),
        wall_clock_seconds=time.time() - start_wall,
        agent="deterministic-fast-path",
        model=model,
        reasoning_effort=reasoning_effort,
        usage=None,
        prompt_path=prompt_log,
        stdout_jsonl=stdout_log,
        stdout_timeline=None,
        stderr_log=stderr_log,
        last_message_path=last_message,
        input_c=input_path,
        input_v=input_v_path,
        annotated_snapshot=annotated_snapshot,
        annotated_cleanup=annotated_cleanup,
    )
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

    # Provision bare-include headers next to the annotated C so symexec resolves
    # both common verification headers and task-local headers such as sll_def.h.
    include_names = {
        "verification_stdlib.h",
        "verification_list.h",
        "int_array_def.h",
        "char_array_def.h",
    }
    include_names.update(re.findall(r'#\s*include\s+"([^"]+)"', input_path.read_text(encoding="utf-8", errors="replace")))
    for _h in sorted(include_names):
        if "/" in _h or "\\" in _h:
            continue
        _src = input_path.parent / _h
        if _src.exists():
            shutil.copy2(_src, REPO_ROOT / "annotated" / _h)

    if input_v_path is not None:
        dst_v = workspace_path / "original" / input_v_path.name
        shutil.copy2(input_v_path, dst_v)
    for dep_v in imported_coq_dependency_paths(input_path):
        dst_v = workspace_path / "original" / dep_v.name
        if input_v_path is not None and dep_v.resolve() == input_v_path.resolve():
            continue
        shutil.copy2(dep_v, dst_v)

    return annotated_c


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run an agent to execute the full verify workflow.")
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
    parser.add_argument("--dry-run", action="store_true", help="Prepare workspace and prompt, but do not invoke the agent.")
    parser.add_argument("--config", default=None, help="Path to agents.json config.")
    parser.add_argument("--agent", choices=["codex", "claude", "kimicode"], default=None)
    parser.add_argument("--codex-bin", default=None, help="Codex CLI binary.")
    parser.add_argument("--claude-bin", default=None, help="Claude CLI binary.")
    parser.add_argument("--kimicode-bin", default=None, help="Kimi Code CLI binary.")
    parser.add_argument("--timeout-seconds", type=int, default=5400, help="Kill the external agent run if it exceeds this wall-clock timeout.")
    parser.add_argument("--restart-context-file", default=None, help="File whose content (e.g. audit check feedback) is injected into the round-1 prompt on a re-run.")
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()

    cfg = agent_config.load(args.config)
    agent = args.agent or cfg.agent("codex")
    builtin_model = DEFAULT_CLAUDE_MODEL if agent == "claude" else ("kimi-code/kimi-for-coding" if agent == "kimicode" else DEFAULT_MODEL)
    model = args.model or cfg.default_model(agent, builtin_model)
    metrics_model = cfg.model_display(agent, model)
    reasoning_effort = (
        agent_config.kimicode_reasoning_effort(args.reasoning_effort, cfg.kimicode_thinking(True))
        if agent == "kimicode"
        else (args.reasoning_effort or cfg.reasoning_effort(DEFAULT_REASONING_EFFORT))
    )
    codex_bin = args.codex_bin or cfg.bin("codex", "codex")
    claude_bin = args.claude_bin or cfg.bin("claude", "claude")
    kimicode_bin = args.kimicode_bin or cfg.bin("kimicode", "kimi")

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
    reasoning_effort_supported = (
        codex_supports_reasoning_effort(codex_bin, REPO_ROOT, agent_env)
        if agent == "codex"
        else False
    )
    claude_effort_supported = (
        agent_config.claude_supports_flag(claude_bin, REPO_ROOT, agent_env, "--effort")
        if agent == "claude"
        else False
    )
    emit_log(f"reasoning_effort={reasoning_effort}")
    emit_log(f"reasoning_effort_supported={reasoning_effort_supported}")
    emit_log(f"claude_effort_supported={claude_effort_supported}")
    run_label = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
    prompt_path = logs_dir / f"agent_prompt_{run_label}.txt"
    stdout_jsonl = logs_dir / f"agent_stdout_{run_label}.jsonl"
    stdout_timeline: Path | None = None
    stderr_log = logs_dir / f"agent_stderr_{run_label}.log"
    last_message_path = logs_dir / f"agent_last_message_{run_label}.txt"

    if args.dry_run:
        prompt = build_prompt(skill_path, input_path, input_v_path, function_name, workspace_path, annotated_c_path, 1)
        ensure_parent(prompt_path)
        prompt_path.write_text(prompt, encoding="utf-8")
        annotated_snapshot = save_annotated_snapshot(workspace_path, annotated_c_path)
        annotated_cleanup = cleanup_global_annotated_after_snapshot(annotated_c_path, annotated_snapshot)
        write_metrics(
            metrics_path(workspace_path),
            status="Success",
            attempts=0,
            last_agent_exit=0,
            start_iso=iso_now(),
            end_iso=iso_now(),
            wall_clock_seconds=0.0,
            agent=agent,
            model=metrics_model,
            reasoning_effort=reasoning_effort,
            usage=None,
            prompt_path=prompt_path,
            stdout_jsonl=stdout_jsonl,
            stdout_timeline=None,
            stderr_log=stderr_log,
            last_message_path=last_message_path,
            input_c=input_path,
            input_v=input_v_path,
            annotated_snapshot=annotated_snapshot,
            annotated_cleanup=annotated_cleanup,
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
        model=metrics_model,
        reasoning_effort=reasoning_effort,
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

    while attempt < 1:
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
        stdout_timeline = logs_dir / f"agent_stdout_{run_label}.jsonl.timeline.tsv"
        stderr_log = logs_dir / f"agent_stderr_{run_label}.log"
        last_message_path = logs_dir / f"agent_last_message_{run_label}.txt"
        if proof_only_mode:
            prompt = build_proof_only_prompt(
                skill_path,
                input_path,
                input_v_path,
                function_name,
                workspace_path,
                annotated_c_path,
                attempt,
                verify_restart_context,
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
                verify_restart_context,
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
                proc_returncode = run_agent_with_timeline(
                    cmd,
                    prompt=prompt,
                    stdout_jsonl=stdout_jsonl,
                    stdout_timeline=stdout_timeline,
                    stderr_log=stderr_log,
                    cwd=REPO_ROOT,
                    timeout=round_timeout,
                    env=agent_env,
                )
                last_message = agent_metrics.extract_claude_last_message(stdout_jsonl)
                if last_message is not None:
                    last_message_path.write_text(last_message, encoding="utf-8")
                elif stdout_jsonl.exists():
                    last_message_path.write_text(stdout_jsonl.read_text(encoding="utf-8", errors="replace"), encoding="utf-8")
            elif agent == "kimicode":
                cmd = [
                    kimicode_bin,
                    "--print",
                    "--yolo",
                    "--afk",
                    "--work-dir",
                    str(REPO_ROOT),
                    "--add-dir",
                    str(REPO_ROOT),
                    "--input-format",
                    "text",
                    "--output-format",
                    "stream-json",
                ]
                if model:
                    cmd.extend(["--model", model])
                cmd.append("--no-thinking" if reasoning_effort == "no-thinking" else "--thinking")
                proc_returncode = run_agent_with_timeline(
                    cmd,
                    prompt=prompt,
                    stdout_jsonl=stdout_jsonl,
                    stdout_timeline=stdout_timeline,
                    stderr_log=stderr_log,
                    cwd=REPO_ROOT,
                    timeout=round_timeout,
                    env=agent_env,
                )
                if stdout_jsonl.exists():
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
                    emit_log(f"codex_reasoning_effort_mode=flag value={reasoning_effort}")
                elif reasoning_effort:
                    cmd.extend(["-c", f"model_reasoning_effort={reasoning_effort}"])
                    emit_log(f"codex_reasoning_effort_mode=config value={reasoning_effort}")
                cmd.append("-")
                proc_returncode = run_agent_with_timeline(
                    cmd,
                    prompt=prompt,
                    stdout_jsonl=stdout_jsonl,
                    stdout_timeline=stdout_timeline,
                    stderr_log=stderr_log,
                    cwd=REPO_ROOT,
                    timeout=round_timeout,
                    env=agent_env,
                )
        except subprocess.TimeoutExpired:
            proc_returncode = 124
            failure_detail = f"external agent run exceeded remaining timeout budget of {round_timeout} seconds"
            emit_log(f"agent_exec_timeout attempt={attempt} detail={failure_detail}")
        end_wall = time.time()
        filter_stderr_in_place(stderr_log)
        if agent == "kimicode":
            try:
                agent_metrics.capture_kimicode_context_usage(
                    logs_dir=workspace_path / "logs",
                    started_at=start_wall,
                    ended_at=end_wall,
                    needles=[str(workspace_path), workspace_stem],
                )
            except Exception as exc:
                emit_log(f"kimicode_usage_capture_error={exc}")

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
        final_result_detail = verify_workspace_final_result(workspace_path)
        if completed:
            emit_log(f"verify_completed={detail}")
            proc_returncode = 0
            break

        if final_result_detail == "metrics_contains_final_result_fail":
            emit_log(f"verify_agent_declared_fail detail={detail}")
            if proc_returncode == 0:
                proc_returncode = 1
            break

        elapsed_total = time.time() - overall_start_wall
        if elapsed_total >= total_budget_seconds:
            emit_log("agent_exec_budget_exhausted_after_attempt")
            if proc_returncode == 0:
                proc_returncode = 124
            break

        if final_result_detail != "metrics_contains_final_result_success":
            emit_log(
                f"verify_incomplete attempt={attempt} final_result={final_result_detail} detail={detail}"
            )
            if proc_returncode == 0:
                proc_returncode = 1
            break

        emit_log(f"verify_success_claim_rejected attempt={attempt} detail={detail}")
        if proc_returncode == 0:
            proc_returncode = 1
        break

    # Drop coqc intermediates (.vo/.glob/.aux).
    # from workspace dirs, keeping .v/.c sources. Never touches the shared QCP tree.
    removed = coq_runner.clean_compile_artifacts(workspace_path / "coq")
    removed += coq_runner.clean_compile_artifacts(workspace_path / "original", recursive=False)
    # The input .v (input/<ds>/<name>.v) compiles in place when goal.v Requires it;
    # drop only THIS problem's intermediates (race-safe under parallel verify_batch).
    for _suf in (".vo", ".glob", ".vok", ".vos"):
        _f = input_path.with_suffix(_suf)
        if _f.exists():
            _f.unlink(); removed.append(str(_f))
    _aux = input_path.parent / f".{input_path.stem}.aux"
    if _aux.exists():
        _aux.unlink(); removed.append(str(_aux))
    emit_log(f"cleaned_compile_artifacts count={len(removed)}")

    overall_end_iso = iso_now()
    annotated_snapshot = save_annotated_snapshot(workspace_path, annotated_c_path)
    annotated_cleanup = cleanup_global_annotated_after_snapshot(annotated_c_path, annotated_snapshot)
    write_metrics(
        metrics_path(workspace_path),
        status="Success" if proc_returncode == 0 else "Fail",
        attempts=attempt,
        last_agent_exit=proc_returncode,
        start_iso=overall_start_iso,
        end_iso=overall_end_iso,
        wall_clock_seconds=time.time() - overall_start_wall,
        agent=agent,
        model=model,
        reasoning_effort=reasoning_effort,
        usage=usage_total,
        prompt_path=prompt_path,
        stdout_jsonl=stdout_jsonl,
        stdout_timeline=stdout_timeline,
        stderr_log=stderr_log,
        last_message_path=last_message_path,
        input_c=input_path,
        input_v=input_v_path,
        annotated_snapshot=annotated_snapshot,
        annotated_cleanup=annotated_cleanup,
    )

    emit_log(f"stdout_jsonl={stdout_jsonl}")
    emit_log(f"stdout_timeline={stdout_timeline if stdout_timeline else '<not recorded>'}")
    emit_log(f"stderr_log={stderr_log}")
    emit_log(f"last_message={last_message_path}")

    print(str(workspace_path))
    return proc_returncode


def metrics_path(workspace_path: Path) -> Path:
    return workspace_path / "logs" / "metrics.md"


if __name__ == "__main__":
    sys.exit(main())

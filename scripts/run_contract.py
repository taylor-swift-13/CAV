#!/usr/bin/env python3
import argparse
import datetime as dt
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
import check_spec_wellformed
import coq_runner


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SKILL = REPO_ROOT / "skills" / "contract" / "SKILL.md"
OUTPUT_ROOT = REPO_ROOT / "output"
INPUT_ROOT = REPO_ROOT / "input"
DEFAULT_MODEL = "gpt-5.4"
DEFAULT_CLAUDE_MODEL = "sonnet"
DEFAULT_REASONING_EFFORT = "medium"
CONTRACT_ILL_FORMED_EXIT = 30
CONTRACT_COQ_EXIT = 31
CONTRACT_MISSING_INPUT_EXIT = 32
CONTRACT_VERIFY_ANNOTATION_EXIT = 33
CONTRACT_V_FORBIDDEN_ASSUMPTION_EXIT = 34
CONTRACT_BAD_INCLUDE_EXIT = 35
ROOT_HEADER_INCLUDES = {
    "verification_stdlib.h",
    "verification_list.h",
    "int_array_def.h",
    "char_array_def.h",
}
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


def ensure_parent(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


def emit_log(message: str) -> None:
    print(f"[contract] {message}", flush=True)


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


def metrics_path(workspace_path: Path) -> Path:
    return workspace_path / "logs" / "metrics.md"


def issues_path(workspace_path: Path) -> Path:
    return workspace_path / "logs" / "issues.md"


def reasoning_path(workspace_path: Path) -> Path:
    return workspace_path / "logs" / "reasoning.md"


def bootstrap_workspace(workspace_path: Path, raw_path: Path) -> dict[str, Path]:
    logs_dir = workspace_path / "logs"
    raw_dir = workspace_path / "raw"
    workspace_input_dir = workspace_path / "input"
    logs_dir.mkdir(parents=True, exist_ok=True)
    raw_dir.mkdir(parents=True, exist_ok=True)
    workspace_input_dir.mkdir(parents=True, exist_ok=True)

    raw_copy = raw_dir / raw_path.name
    shutil.copy2(raw_path, raw_copy)
    return {
        "logs_dir": logs_dir,
        "raw_dir": raw_dir,
        "workspace_input_dir": workspace_input_dir,
        "raw_copy": raw_copy,
    }


def build_prompt(
    skill_path: Path,
    raw_path: Path,
    workspace_path: Path,
    target_c_path: Path,
    target_v_path: Path,
    function_name: str,
    attempt: int,
    restart_context: str | None = None,
) -> str:
    lines = [
        f"Follow this skill as the complete workflow: {skill_path}",
        "",
        "Inputs:",
        f"- Raw markdown: `{raw_path}`",
        f"- Target function: `{function_name}`",
        f"- Workspace: `{workspace_path}`",
        f"- Output C: `{target_c_path}`",
        f"- Optional output V: `{target_v_path}`",
    ]
    if attempt > 1:
        lines += ["", f"Attempt: {attempt} (retry — the previous contract attempt failed its syntax check)."]
    if restart_context:
        lines += ["", "Restart feedback (must be addressed before finishing this contract run):", restart_context.rstrip()]
    return "\n".join(lines) + "\n"


def write_metrics(
    path: Path,
    *,
    status: str,
    exit_code: int,
    start_iso: str,
    end_iso: str,
    wall_seconds: float,
    agent: str,
    model: str,
    reasoning_effort: str,
    prompt_path: Path,
    stdout_jsonl: Path,
    stderr_log: Path,
    last_message_path: Path,
    target_c: Path,
    target_v: Path,
    usage: dict[str, int] | None,
    dry_run: bool,
    wellformed: str = "not_run",
    wellformed_exit: int | None = None,
) -> None:
    lines = [
        "# Contract Metrics",
        "",
        "- Stage: `contract`",
        f"- Status: `{status}`",
        f"- Dry run: `{str(dry_run).lower()}`",
        f"- Exit code: `{exit_code}`",
        f"- Start time: `{start_iso}`",
        f"- End time: `{end_iso}`",
        f"- Wall-clock time (seconds): `{wall_seconds:.2f}`",
        f"- Agent: `{agent}`",
        f"- Model: `{model or 'n/a'}`",
        f"- Reasoning effort: `{reasoning_effort or 'n/a'}`",
        f"- Output C: `{target_c}`",
        f"- Output V: `{target_v if target_v.exists() else '<not created>'}`",
        f"- Contract syntax check wellformed gate: `{wellformed}` (symexec exit `{wellformed_exit if wellformed_exit is not None else 'n/a'}`)",
        f"- Prompt file: `{prompt_path}`",
        f"- Agent stdout: `{stdout_jsonl}`",
        f"- Agent stderr: `{stderr_log}`",
        f"- Agent last message: `{last_message_path}`",
    ]
    lines.extend(agent_metrics.usage_lines(
        usage, prompt_path=prompt_path, last_message_path=last_message_path))
    lines.extend(["- Experience updates: none", f"Final Result: {status}"])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def update_issues_on_failure(issues_md: Path, stage: str, exit_code: int, stderr_log: Path, detail: str | None = None) -> None:
    issues_md.parent.mkdir(parents=True, exist_ok=True)
    if issues_md.exists():
        existing = issues_md.read_text(encoding="utf-8").rstrip() + "\n\n"
    else:
        existing = "# Contract Issues\n\n"
    block = (
        "## External Codex Failure\n\n"
        f"- Stage: `{stage}`\n"
        f"- Exit code: `{exit_code}`\n"
        f"- Stderr log: `{stderr_log}`\n"
    )
    if detail:
        block += f"- Detail: `{detail}`\n"
    issues_md.write_text(existing + block, encoding="utf-8")


def update_issues_on_wellformed_failure(issues_md: Path, detail: str, target_c: Path) -> None:
    issues_md.parent.mkdir(parents=True, exist_ok=True)
    if issues_md.exists():
        existing = issues_md.read_text(encoding="utf-8").rstrip() + "\n\n"
    else:
        existing = "# Contract Issues\n\n"
    block = (
        "## Contract Well-Formedness Failure\n\n"
        "- Stage: `contract-wellformed-gate`\n"
        f"- Exit code: `{CONTRACT_ILL_FORMED_EXIT}`\n"
        f"- Generated C: `{target_c}`\n"
        f"- Detail: `{detail}`\n\n"
        "The generated contract is not parseable by QCP symexec, so the pipeline "
        "must retry contract generation before eval or verify.\n"
    )
    issues_md.write_text(existing + block, encoding="utf-8")


def update_issues_on_contract_syntax_check_failure(issues_md: Path, stage: str, exit_code: int, detail: str) -> None:
    issues_md.parent.mkdir(parents=True, exist_ok=True)
    if issues_md.exists():
        existing = issues_md.read_text(encoding="utf-8").rstrip() + "\n\n"
    else:
        existing = "# Contract Issues\n\n"
    block = (
        "## Contract Syntax Check Failure\n\n"
        f"- Stage: `{stage}`\n"
        f"- Exit code: `{exit_code}`\n"
        f"- Detail: `{detail}`\n\n"
        "The contract agent must fix this before eval or verify can start.\n"
    )
    issues_md.write_text(existing + block, encoding="utf-8")


def check_input_v_if_present(input_v: Path, workspace_path: Path) -> tuple[bool, int | None, str]:
    if not input_v.exists():
        return True, None, "input V not present"
    try:
        rc, out, err = coq_runner.run_coqc(
            input_v,
            extra_q=[(str(input_v.parent), "")],
            timeout_seconds=120,
        )
    finally:
        coq_runner.clean_compile_artifacts(input_v.parent, recursive=False)
    log_path = workspace_path / "logs" / "input_v_coqc.log"
    log_path.write_text(
        f"$ coqc {input_v}\nrc={rc}\n\n# stdout\n{out}\n# stderr\n{err}\n",
        encoding="utf-8",
    )
    if rc == 0:
        return True, rc, f"input V compiled: {log_path}"
    return False, rc, f"input V failed to compile: {log_path}"


def check_no_verify_annotations(input_c: Path, workspace_path: Path) -> tuple[bool, str]:
    """Contract output must not contain verify-stage Inv/Assert/which-implies blocks."""
    text = input_c.read_text(encoding="utf-8", errors="replace")
    log_path = workspace_path / "logs" / "contract_annotation_gate.log"
    findings: list[str] = []
    for match in re.finditer(r"/\*@(.*?)\*/", text, flags=re.DOTALL):
        body = match.group(1)
        line = text[:match.start()].count("\n") + 1
        if re.search(r"\bInv\b|\bAssert\b|\bwhich\s+implies\b", body, flags=re.IGNORECASE):
            snippet = re.sub(r"\s+", " ", body).strip()[:300]
            findings.append(f"line {line}: {snippet}")
    if findings:
        log_path.write_text(
            "Contract annotation gate failed: verify-stage annotation found in input C.\n"
            + "\n".join(f"- {item}" for item in findings)
            + "\n",
            encoding="utf-8",
        )
        return False, f"verify-stage annotation in contract C: {log_path}"
    log_path.write_text("Contract annotation gate passed.\n", encoding="utf-8")
    return True, f"contract annotation gate passed: {log_path}"


def check_root_header_includes(input_c: Path, workspace_path: Path) -> tuple[bool, str]:
    """Root headers must be reachable from both input/ and annotated/."""
    text = input_c.read_text(encoding="utf-8", errors="replace")
    log_path = workspace_path / "logs" / "contract_include_gate.log"
    findings: list[str] = []
    include_re = re.compile(r'^\s*#\s*include\s+"([^"]+)"', flags=re.MULTILINE)
    lines = text.splitlines()
    for match in include_re.finditer(text):
        include_path = match.group(1)
        header = Path(include_path).name
        if header not in ROOT_HEADER_INCLUDES:
            continue
        expected = header  # headers are co-located in the dataset folder; use bare include
        if include_path != expected:
            line_no = text[:match.start()].count("\n") + 1
            line = lines[line_no - 1].strip() if line_no <= len(lines) else match.group(0)
            findings.append(
                f"line {line_no}: `{line}` includes root header `{header}` as "
                f"`{include_path}`; use `{expected}`"
            )
    if findings:
        log_path.write_text(
            "Contract include gate failed: root headers must be included by bare name.\n"
            "The verification headers are copied into each dataset folder, so use `#include \"<header>\"` with no path.\n"
            + "\n".join(f"- {item}" for item in findings)
            + "\n",
            encoding="utf-8",
        )
        return False, f"bad root header include path: {log_path}"
    log_path.write_text("Contract include gate passed.\n", encoding="utf-8")
    return True, f"contract include gate passed: {log_path}"


def check_input_v_has_only_definitions(input_v: Path, workspace_path: Path) -> tuple[bool, str]:
    """Optional input .v may define logic, but must not introduce assumptions."""
    if not input_v.exists():
        return True, "input V not present"
    text = input_v.read_text(encoding="utf-8", errors="replace")
    log_path = workspace_path / "logs" / "input_v_definition_gate.log"
    forbidden = re.compile(
        r"^\s*(Axiom|Hypothesis|Parameter|Parameters|Conjecture|Variable|Variables|Declare)\b"
        r"|\b(Admitted|admit|Abort)\b",
        flags=re.MULTILINE,
    )
    findings = []
    lines = text.splitlines()
    for match in forbidden.finditer(text):
        line_no = text[:match.start()].count("\n") + 1
        line = lines[line_no - 1].strip() if line_no <= len(lines) else match.group(0)
        findings.append(f"line {line_no}: {line[:300]}")
    if findings:
        log_path.write_text(
            "Input V definition gate failed: .v contains assumptions/stubs instead of definitions only.\n"
            + "\n".join(f"- {item}" for item in findings)
            + "\n",
            encoding="utf-8",
        )
        return False, f"input V contains forbidden assumptions/stubs: {log_path}"
    log_path.write_text("Input V definition gate passed.\n", encoding="utf-8")
    return True, f"input V definition gate passed: {log_path}"


def run_contract_syntax_check(target_c: Path, target_v: Path, workspace_path: Path) -> tuple[bool, int, str, str, int | None]:
    if not target_c.exists():
        return False, CONTRACT_MISSING_INPUT_EXIT, f"missing generated C: {target_c}", "not_run", None
    annotation_ok, annotation_detail = check_no_verify_annotations(target_c, workspace_path)
    if not annotation_ok:
        return False, CONTRACT_VERIFY_ANNOTATION_EXIT, annotation_detail, "not_run", None
    include_ok, include_detail = check_root_header_includes(target_c, workspace_path)
    if not include_ok:
        return False, CONTRACT_BAD_INCLUDE_EXIT, include_detail, "not_run", None
    wellformed, wellformed_exit, wf_detail = check_spec_wellformed.check(target_c)
    emit_log(f"wellformed={wellformed} symexec_exit={wellformed_exit} detail={wf_detail}")
    if wellformed != "well_formed":
        return False, CONTRACT_ILL_FORMED_EXIT, wf_detail, wellformed, wellformed_exit
    v_def_ok, v_def_detail = check_input_v_has_only_definitions(target_v, workspace_path)
    if not v_def_ok:
        return False, CONTRACT_V_FORBIDDEN_ASSUMPTION_EXIT, v_def_detail, wellformed, wellformed_exit
    v_ok, v_exit, v_detail = check_input_v_if_present(target_v, workspace_path)
    if not v_ok:
        return False, CONTRACT_COQ_EXIT, f"{v_detail} (coqc exit {v_exit})", wellformed, wellformed_exit
    return True, 0, f"{annotation_detail}; {include_detail}; {v_def_detail}; {v_detail}", wellformed, wellformed_exit


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


def contract_retry_feedback(
    *,
    attempt: int,
    proc_returncode: int,
    wellformed: str,
    wellformed_exit: int | None,
    detail: str | None,
    target_c: Path,
) -> str:
    lines = [
        f"Contract attempt {attempt} failed.",
        "",
        f"- Agent exit code: `{proc_returncode}`",
        f"- Syntax check wellformed gate: `{wellformed}`",
        f"- Symexec exit: `{wellformed_exit if wellformed_exit is not None else 'n/a'}`",
    ]
    if detail:
        lines.append(f"- Detail: `{detail}`")
    if target_c.exists():
        lines.extend([
            "",
            "Generated C from the failed attempt:",
            "",
            "```c",
            target_c.read_text(encoding="utf-8", errors="replace").rstrip(),
            "```",
        ])
    lines.extend([
        "",
        "Required next action: regenerate or edit the contract so input C has no verify-stage Inv/Assert/which-implies annotations, root headers use ../<header> from input/, optional input V contains definitions only, and the QCP wellformed gate passes before eval or verify starts.",
    ])
    return "\n".join(lines)


def ensure_reasoning_placeholder(reasoning_md: Path, stage: str, detail: str | None = None) -> None:
    if reasoning_md.exists():
        return
    lines = [
        "# Contract Reasoning",
        "",
        "## Unavailable",
        "",
        f"- This file was not produced by the contract run because stage `{stage}` failed before reasoning was written.",
    ]
    if detail:
        lines.append(f"- Failure detail: `{detail}`")
    reasoning_md.write_text("\n".join(lines) + "\n", encoding="utf-8")


def snapshot_generated_inputs(workspace_path: Path, input_c: Path, input_v: Path) -> None:
    generated_input_dir = workspace_path / "input"
    generated_input_dir.mkdir(parents=True, exist_ok=True)
    if input_c.exists():
        shutil.copy2(input_c, generated_input_dir / input_c.name)
    if input_v.exists():
        shutil.copy2(input_v, generated_input_dir / input_v.name)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run an agent to produce contract-stage inputs from raw markdown.")
    parser.add_argument("input_md", help="Path to raw markdown input, relative to repo root or absolute.")
    parser.add_argument("function_name_positional", nargs="?", help="Optional target function name. Kept for CLI compatibility.")
    parser.add_argument("--function-name", help="Explicit target function name. Defaults to markdown stem.")
    parser.add_argument("--skill", default=str(DEFAULT_SKILL), help="Path to contract skill markdown.")
    parser.add_argument("--workspace-name", help="Explicit workspace stem; defaults to markdown stem.")
    parser.add_argument("--dataset", default=None, help="Dataset label; writes input under input/<dataset>/.")
    parser.add_argument("--timestamp", help="Explicit contract timestamp; defaults to current local time.")
    parser.add_argument("--config", default=None, help="Path to agents.json config.")
    parser.add_argument("--agent", choices=["codex", "claude", "kimicode"], default=None)
    parser.add_argument("--model", default=None, help="Agent model.")
    parser.add_argument("--reasoning-effort", default=None, help="Agent reasoning effort.")
    parser.add_argument("--dry-run", action="store_true", help="Prepare workspace and prompt, but do not invoke the agent.")
    parser.add_argument("--codex-bin", default=None, help="Codex CLI binary.")
    parser.add_argument("--claude-bin", default=None, help="Claude CLI binary.")
    parser.add_argument("--kimicode-bin", default=None, help="Kimi Code CLI binary.")
    parser.add_argument("--timeout-seconds", type=int, default=300, help="Kill the external agent run if it exceeds this wall-clock timeout.")
    parser.add_argument("--restart-context-file", default=None, help="File whose content (e.g. eval critic findings) is injected into the prompt on a re-run.")
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()

    raw_path = Path(args.input_md)
    if not raw_path.is_absolute():
        raw_path = (REPO_ROOT / raw_path).resolve()
    skill_path = Path(args.skill)
    if not skill_path.is_absolute():
        skill_path = (REPO_ROOT / skill_path).resolve()

    if not raw_path.exists():
        print(f"input markdown not found: {raw_path}", file=sys.stderr)
        return 2
    if raw_path.suffix != ".md":
        print(f"input markdown must be a .md file: {raw_path}", file=sys.stderr)
        return 2
    if not skill_path.exists():
        print(f"skill file not found: {skill_path}", file=sys.stderr)
        return 2

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

    workspace_stem = args.workspace_name or raw_path.stem
    workspace_timestamp = args.timestamp or timestamp_now()
    workspace_path = OUTPUT_ROOT / f"contract_{workspace_timestamp}_{workspace_stem}"
    bootstrap_workspace(workspace_path, raw_path)
    emit_log(f"workspace={workspace_path}")

    function_name = args.function_name or args.function_name_positional or raw_path.stem
    _input_dir = (INPUT_ROOT / args.dataset) if getattr(args, "dataset", None) else INPUT_ROOT
    _input_dir.mkdir(parents=True, exist_ok=True)
    # Co-locate verification headers so generated C can include them by bare name.
    for _h in ROOT_HEADER_INCLUDES:
        _src = REPO_ROOT / _h
        if _src.exists() and not (_input_dir / _h).exists():
            shutil.copy2(_src, _input_dir / _h)
    target_c_path = _input_dir / f"{raw_path.stem}.c"
    target_v_path = _input_dir / f"{raw_path.stem}.v"
    emit_log(f"input_md={raw_path}")
    emit_log(f"function_name={function_name}")
    emit_log(f"target_c={target_c_path}")
    emit_log(f"target_v={target_v_path}")

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
    emit_log(f"agent={agent}")
    emit_log(f"model={model}")
    emit_log(f"reasoning_effort={reasoning_effort}")
    emit_log(f"reasoning_effort_supported={reasoning_effort_supported}")
    emit_log(f"claude_effort_supported={claude_effort_supported}")
    restart_context = None
    if args.restart_context_file:
        rc_path = Path(args.restart_context_file)
        if rc_path.exists():
            restart_context = rc_path.read_text(encoding="utf-8", errors="replace")

    if args.dry_run:
        run_label = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
        prompt_path = logs_dir / f"agent_prompt_{run_label}.txt"
        stdout_jsonl = logs_dir / f"agent_stdout_{run_label}.jsonl"
        stderr_log = logs_dir / f"agent_stderr_{run_label}.log"
        last_message_path = logs_dir / f"agent_last_message_{run_label}.txt"
        prompt = build_prompt(
            skill_path,
            raw_path,
            workspace_path,
            target_c_path,
            target_v_path,
            function_name,
            1,
            restart_context,
        )
        ensure_parent(prompt_path)
        prompt_path.write_text(prompt, encoding="utf-8")
        write_metrics(
            metrics_path(workspace_path),
            status="Success",
            exit_code=0,
            start_iso=iso_now(),
            end_iso=iso_now(),
            wall_seconds=0.0,
            agent=agent,
            model=metrics_model,
            reasoning_effort=reasoning_effort,
            prompt_path=prompt_path,
            stdout_jsonl=stdout_jsonl,
            stderr_log=stderr_log,
            last_message_path=last_message_path,
            target_c=target_c_path,
            target_v=target_v_path,
            usage=None,
            dry_run=True,
        )
        emit_log("dry_run=true")
        print(str(workspace_path))
        return 0

    overall_start_wall = time.time()
    overall_start_iso = iso_now()
    total_budget_seconds = args.timeout_seconds
    attempt = 0
    proc_returncode = 1
    status = "Fail"
    failure_detail = None
    prompt_path = stdout_jsonl = stderr_log = last_message_path = logs_dir / "not_started"
    usage_total: dict[str, int] | None = None
    wellformed, wellformed_exit = "not_run", None

    if restart_context:
        append_continue(logs_dir, "overturn", restart_context)

    while True:
        attempt += 1
        remaining = total_budget_seconds - (time.time() - overall_start_wall)
        if remaining <= 0:
            proc_returncode = 124
            failure_detail = "contract retry budget exhausted"
            emit_log("agent_exec_budget_exhausted")
            break

        retry_context = None
        continue_path = logs_dir / "continue.md"
        if continue_path.exists():
            retry_context = continue_path.read_text(encoding="utf-8", errors="replace")
        run_label = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
        prompt_path = logs_dir / f"agent_prompt_{run_label}.txt"
        stdout_jsonl = logs_dir / f"agent_stdout_{run_label}.jsonl"
        stderr_log = logs_dir / f"agent_stderr_{run_label}.log"
        last_message_path = logs_dir / f"agent_last_message_{run_label}.txt"
        prompt = build_prompt(
            skill_path,
            raw_path,
            workspace_path,
            target_c_path,
            target_v_path,
            function_name,
            attempt,
            retry_context,
        )
        ensure_parent(prompt_path)
        prompt_path.write_text(prompt, encoding="utf-8")

        round_timeout = int(max(1, remaining))
        emit_log(f"agent_exec_start attempt={attempt} round_timeout_seconds={round_timeout} total_budget_seconds={total_budget_seconds}")
        start_wall = time.time()
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
        filter_stderr_in_place(stderr_log)

        snapshot_generated_inputs(workspace_path, target_c_path, target_v_path)
        usage_total = agent_metrics.add_usage(usage_total, agent_metrics.parse_usage(agent, stdout_jsonl))

        gate_ok = False
        gate_exit = proc_returncode
        gate_detail = failure_detail
        if proc_returncode == 0:
            try:
                gate_ok, gate_exit, gate_detail, wellformed, wellformed_exit = run_contract_syntax_check(
                    target_c_path,
                    target_v_path,
                    workspace_path,
                )
            except Exception as exc:  # noqa: BLE001
                gate_ok = False
                gate_exit = CONTRACT_ILL_FORMED_EXIT
                gate_detail = f"contract syntax check failed unexpectedly: {exc}"
                emit_log(f"contract_syntax_check_failed_unexpected: {exc}")

        if proc_returncode == 0 and gate_ok:
            status = "Success"
            emit_log(f"agent_exec_completed attempt={attempt} exit_code=0")
            break

        if proc_returncode == 0:
            proc_returncode = gate_exit
            failure_detail = gate_detail
            if proc_returncode == CONTRACT_ILL_FORMED_EXIT:
                update_issues_on_wellformed_failure(
                    issues_path(workspace_path),
                    gate_detail or "contract is ill-formed",
                    target_c_path,
                )
            else:
                update_issues_on_contract_syntax_check_failure(
                    issues_path(workspace_path),
                    "contract-syntax-check",
                    proc_returncode,
                    gate_detail or "contract syntax check failed",
                )
        else:
            update_issues_on_failure(
                issues_path(workspace_path),
                "external-agent-run",
                proc_returncode,
                stderr_log,
                failure_detail,
            )

        feedback = contract_retry_feedback(
            attempt=attempt,
            proc_returncode=proc_returncode,
            wellformed=wellformed,
            wellformed_exit=wellformed_exit,
            detail=failure_detail or gate_detail,
            target_c=target_c_path,
        )
        append_continue(logs_dir, f"retry-after-attempt-{attempt}", feedback)
        emit_log(f"contract_incomplete_retrying attempt={attempt} detail={failure_detail or gate_detail or proc_returncode}")

        if proc_returncode == 124:
            break

    end_iso = iso_now()

    write_metrics(
        metrics_path(workspace_path),
        status=status,
        exit_code=proc_returncode,
        start_iso=overall_start_iso,
        end_iso=end_iso,
        wall_seconds=time.time() - overall_start_wall,
        agent=agent,
        model=metrics_model,
        reasoning_effort=reasoning_effort,
        prompt_path=prompt_path,
        stdout_jsonl=stdout_jsonl,
        stderr_log=stderr_log,
        last_message_path=last_message_path,
        target_c=target_c_path,
        target_v=target_v_path,
        usage=usage_total,
        dry_run=False,
        wellformed=wellformed,
        wellformed_exit=wellformed_exit,
    )

    if proc_returncode != 0:
        ensure_reasoning_placeholder(
            reasoning_path(workspace_path),
            "external-agent-run",
            failure_detail,
        )
        if proc_returncode not in (CONTRACT_ILL_FORMED_EXIT, CONTRACT_COQ_EXIT, CONTRACT_MISSING_INPUT_EXIT, CONTRACT_BAD_INCLUDE_EXIT):
            update_issues_on_failure(
                issues_path(workspace_path),
                "external-agent-run",
                proc_returncode,
                stderr_log,
                failure_detail,
            )
        emit_log(f"agent_exec_failed exit_code={proc_returncode}")
    else:
        emit_log(f"agent_exec_completed exit_code=0 attempts={attempt}")

    emit_log(f"stdout_jsonl={stdout_jsonl}")
    emit_log(f"stderr_log={stderr_log}")
    emit_log(f"last_message={last_message_path}")

    print(str(workspace_path))
    return proc_returncode


if __name__ == "__main__":
    sys.exit(main())

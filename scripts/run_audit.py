#!/usr/bin/env python3
"""Run the audit stage with codex or claude-code as the backend agent.

Audit consumes a verify workspace (or an explicit original/verified pair) and
detects anti-cheating violations: contract weakening, unchecked axioms,
unproven lemmas, assume/Admitted, suppressions, reflection / runtime exit.
The deterministic detection is done by
scripts/audit_jml.py; this runner orchestrates the agent that renders the
findings into a justified audit verdict.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import agent_config
import agent_metrics


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SKILL = REPO_ROOT / "skills" / "audit" / "SKILL.md"
OUTPUT_ROOT = REPO_ROOT / "output"

AGENT_CODEX = "codex"
AGENT_CLAUDE = "claude"
DEFAULT_AGENT = AGENT_CODEX

DEFAULT_MODEL_CODEX = "gpt-5.4"
DEFAULT_MODEL_CLAUDE = "sonnet"
DEFAULT_REASONING_EFFORT = "medium"

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


def emit(message: str) -> None:
    print(f"[audit] {message}", flush=True)


def build_agent_env(logs_dir: Path) -> dict[str, str]:
    env = os.environ.copy()
    for name, dirname in {
        "XDG_CACHE_HOME": ".agent_cache",
        "XDG_STATE_HOME": ".state",
        "XDG_DATA_HOME": ".data",
        "XDG_CONFIG_HOME": ".config",
        "TMPDIR": ".tmp",
        "TMP": ".tmp",
        "TEMP": ".tmp",
    }.items():
        path = logs_dir / dirname
        path.mkdir(parents=True, exist_ok=True)
        env[name] = str(path)
    return env


def codex_supports_reasoning_effort(codex_bin: str, env: dict[str, str]) -> bool:
    try:
        proc = subprocess.run(
            [codex_bin, "exec", "--help"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            cwd=REPO_ROOT,
            env=env,
            timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return False
    return "--reasoning-effort" in proc.stdout


def claude_supports_flag(claude_bin: str, env: dict[str, str], flag: str) -> bool:
    try:
        proc = subprocess.run(
            [claude_bin, "--help"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            cwd=REPO_ROOT,
            env=env,
            timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return False
    return flag in proc.stdout


def filter_stderr(path: Path) -> None:
    if not path.exists():
        return
    kept = []
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        if any(pattern in line for pattern in NOISE_PATTERNS):
            continue
        kept.append(line)
    path.write_text("\n".join(kept) + ("\n" if kept else ""), encoding="utf-8")


def resolve_workspace_inputs(args: argparse.Namespace) -> tuple[Path, Path, str]:
    """Returns (original_java, verified_java, name_stem)."""
    if args.workspace:
        ws = Path(args.workspace).resolve()
        original_dir = ws / "original"
        verified_dir = ws / "verified"
        if not original_dir.is_dir() or not verified_dir.is_dir():
            raise SystemExit(f"verify workspace missing original/ or verified/: {ws}")
        candidates_orig = sorted(original_dir.glob("*.java"))
        candidates_ver = sorted(verified_dir.glob("*.java"))
        if not candidates_orig or not candidates_ver:
            raise SystemExit(f"no .java files under {original_dir} or {verified_dir}")
        return candidates_orig[0], candidates_ver[0], candidates_ver[0].stem
    if not args.original or not args.verified:
        raise SystemExit("either --workspace or both --original and --verified are required")
    original = Path(args.original).resolve()
    verified = Path(args.verified).resolve()
    if not original.exists():
        raise SystemExit(f"original not found: {original}")
    if not verified.exists():
        raise SystemExit(f"verified not found: {verified}")
    return original, verified, verified.stem


def run_audit_script(verified: Path, baseline: Path, findings_out: Path, logs_dir: Path) -> int:
    proc = subprocess.run(
        [
            sys.executable,
            str(REPO_ROOT / "scripts" / "audit_jml.py"),
            str(verified),
            "--baseline",
            str(baseline),
            "--findings",
            str(findings_out),
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        cwd=REPO_ROOT,
    )
    (logs_dir / "cheating_scan_stdout.log").write_text(proc.stdout, encoding="utf-8")
    (logs_dir / "cheating_scan_stderr.log").write_text(proc.stderr, encoding="utf-8")
    return proc.returncode


def run_openjml_cross_check(verified: Path, logs_dir: Path) -> int:
    proc = subprocess.run(
        [str(REPO_ROOT / "scripts" / "run_openjml_verify.sh"), str(verified)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        cwd=REPO_ROOT,
    )
    (logs_dir / "openjml_cross_check_stdout.log").write_text(proc.stdout, encoding="utf-8")
    (logs_dir / "openjml_cross_check_stderr.log").write_text(proc.stderr, encoding="utf-8")
    return proc.returncode


def build_prompt(
    skill: Path,
    workspace: Path,
    original_java: Path,
    verified_java: Path,
    findings_json: Path,
    findings_md: Path,
    final_result_md: Path,
    openjml_exit: int,
    audit_script_exit: int,
) -> str:
    return f"""Use this skill as the complete workflow:
{skill}

Audit inputs (deterministic detection has already run):
- Original Java: `{original_java}`
- Verified Java: `{verified_java}`
- Workspace: `{workspace}`
- Findings JSON (produced by scripts/audit_jml.py): `{findings_json}`
- Audit script exit code: `{audit_script_exit}` (non-zero means at least one error-severity finding)
- OpenJML cross-check exit code: `{openjml_exit}` (0 = passed)

Audit outputs you must produce:
- `{findings_md}` — human-readable rendering of every finding, including
  remediation, and any `accepted_false_positive` justification with a cited
  JML rule.
- `{final_result_md}` — overall audit verdict on the first line:
  `- Audit verdict: VerifiedClean`, `VerifiedWithWarnings`, or `NotVerified`.
  Justify the verdict in the body.
- `{workspace / 'logs' / 'reasoning.md'}` — per-finding analysis.
- `{workspace / 'logs' / 'issues.md'}` — unresolved questions.
- `{workspace / 'logs' / 'metrics.md'}` — must end with either
  `Final Result: Success` or `Final Result: Fail` per the skill rules.

Rules:
- Treat `{original_java}` and `{verified_java}` as read-only evidence.
- Produce audit reports under the audit workspace.
- Every `error`-severity finding either remains an error in the verdict or
  carries an `accepted_false_positive` justification citing a specific JML
  rule.
- `Audit verdict: NotVerified` is treated as `Final Result: Fail`.
- A passing OpenJML cross-check combined with unresolved error-severity
  findings is the most damning signal — the proof went through because of
  cheating. Flag this case explicitly.
"""


def run_codex_agent(
    *,
    codex_bin: str,
    model: str,
    reasoning_effort: str,
    timeout_seconds: int,
    prompt: str,
    stdout_path: Path,
    stderr_path: Path,
    last_message_path: Path,
    env: dict[str, str],
) -> int:
    supports_effort = codex_supports_reasoning_effort(codex_bin, env)
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
    if reasoning_effort and supports_effort:
        cmd.extend(["--reasoning-effort", reasoning_effort])
    cmd.append("-")
    try:
        with stdout_path.open("w", encoding="utf-8") as out_f, stderr_path.open("w", encoding="utf-8") as err_f:
            proc = subprocess.run(
                cmd,
                input=prompt,
                text=True,
                stdout=out_f,
                stderr=err_f,
                cwd=REPO_ROOT,
                env=env,
                timeout=timeout_seconds,
            )
        return proc.returncode
    except subprocess.TimeoutExpired:
        stderr_path.write_text("Codex execution timed out.\n", encoding="utf-8")
        return 124


def run_claude_agent(
    *,
    claude_bin: str,
    model: str,
    reasoning_effort: str,
    timeout_seconds: int,
    prompt: str,
    stdout_path: Path,
    stderr_path: Path,
    last_message_path: Path,
    env: dict[str, str],
) -> int:
    supports_effort = claude_supports_flag(claude_bin, env, "--effort")
    supports_json = claude_supports_flag(claude_bin, env, "--output-format")
    cmd = [
        claude_bin,
        "--print",
        "--dangerously-skip-permissions",
        "--add-dir",
        str(REPO_ROOT),
    ]
    if model:
        cmd.extend(["--model", model])
    if reasoning_effort and supports_effort:
        cmd.extend(["--effort", reasoning_effort])
    if supports_json:
        cmd.extend(["--output-format", "json"])
    try:
        with stdout_path.open("w", encoding="utf-8") as out_f, stderr_path.open("w", encoding="utf-8") as err_f:
            proc = subprocess.run(
                cmd,
                input=prompt,
                text=True,
                stdout=out_f,
                stderr=err_f,
                cwd=REPO_ROOT,
                env=env,
                timeout=timeout_seconds,
            )
        exit_code = proc.returncode
    except subprocess.TimeoutExpired:
        stderr_path.write_text("Claude execution timed out.\n", encoding="utf-8")
        return 124

    if stdout_path.exists():
        text = stdout_path.read_text(encoding="utf-8", errors="replace")
        last_text = text
        if supports_json and text.strip().startswith("{"):
            try:
                obj = json.loads(text)
                if isinstance(obj, dict):
                    if isinstance(obj.get("result"), str):
                        last_text = obj["result"]
                    elif isinstance(obj.get("messages"), list) and obj["messages"]:
                        last = obj["messages"][-1]
                        if isinstance(last, dict) and isinstance(last.get("content"), str):
                            last_text = last["content"]
            except json.JSONDecodeError:
                pass
        last_message_path.write_text(last_text, encoding="utf-8")
    else:
        last_message_path.write_text("", encoding="utf-8")
    return exit_code


def read_audit_verdict(final_result: Path) -> str | None:
    if not final_result.exists():
        return None
    for raw in final_result.read_text(encoding="utf-8", errors="replace").splitlines():
        # Tolerate markdown decoration: "## Audit verdict:", "- **Audit verdict:**", etc.
        line = raw.strip().lstrip("#*->` ").strip()
        if line.lower().startswith("audit verdict:"):
            return line.split(":", 1)[1].strip().strip("*`").strip()
    return None


def write_metrics(
    path: Path,
    *,
    agent: str,
    status: str,
    dry_run: bool,
    exit_code: int,
    start_iso: str,
    end_iso: str,
    wall_seconds: float,
    model: str,
    reasoning_effort: str,
    original_java: Path,
    verified_java: Path,
    prompt_path: Path,
    stdout_path: Path,
    stderr_path: Path,
    last_message_path: Path,
    usage: dict[str, int] | None,
    audit_script_exit: int | None,
    openjml_exit: int | None,
    error_findings: int,
    warning_findings: int,
    audit_verdict: str | None,
    judgment: str,
) -> None:
    lines = [
        "# Audit Metrics",
        "",
        "- Stage: `audit`",
        f"- Agent: `{agent}`",
        f"- Status: `{status}`",
        f"- Dry run: `{str(dry_run).lower()}`",
        f"- Agent exit code: `{exit_code}`",
        f"- Start time: `{start_iso}`",
        f"- End time: `{end_iso}`",
        f"- Wall-clock time (seconds): `{wall_seconds:.2f}`",
        f"- Model: `{model}`",
        f"- Reasoning effort: `{reasoning_effort}`",
        f"- Original Java: `{original_java}`",
        f"- Verified Java: `{verified_java}`",
        f"- Audit script exit code: `{audit_script_exit if audit_script_exit is not None else 'not_run'}`",
        f"- OpenJML cross-check exit code: `{openjml_exit if openjml_exit is not None else 'not_run'}`",
        f"- Error-severity findings: `{error_findings}`",
        f"- Warning-severity findings: `{warning_findings}`",
        f"- Audit verdict: `{audit_verdict if audit_verdict else 'unset'}`",
        f"- Final judgment: `{judgment}`",
        f"- Prompt file: `{prompt_path}`",
        f"- Agent stdout: `{stdout_path}`",
        f"- Agent stderr: `{stderr_path}`",
        f"- Agent last message: `{last_message_path}`",
    ]
    lines.extend(agent_metrics.usage_lines(
        usage, prompt_path=prompt_path, last_message_path=last_message_path))
    lines.extend(["- Experience: consolidated at end of flow", f"Final Result: {status}"])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def count_findings(findings_json: Path) -> tuple[int, int]:
    if not findings_json.exists():
        return 0, 0
    try:
        data = json.loads(findings_json.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return 0, 0
    error = warning = 0
    for f in data.get("findings", []):
        sev = f.get("severity")
        if sev == "error":
            error += 1
        elif sev == "warning":
            warning += 1
    return error, warning


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run audit with codex or claude-code as the agent backend.")
    parser.add_argument("--workspace", help="Path to a verify workspace (output/verify_<ts>_<name>/).")
    parser.add_argument("--original", help="Original contract-stage Java file.")
    parser.add_argument("--verified", help="Verified Java file.")
    parser.add_argument("--skill", default=str(DEFAULT_SKILL), help="Path to audit skill.")
    parser.add_argument("--workspace-name", help="Audit workspace stem. Defaults to verified filename stem.")
    parser.add_argument("--timestamp", help="Explicit timestamp. Defaults to current local time.")
    parser.add_argument("--config", default=None, help="Path to agents.json config.")
    parser.add_argument(
        "--agent",
        choices=[AGENT_CODEX, AGENT_CLAUDE],
        default=None,
        help="Which CLI to drive: 'codex' or 'claude'. Defaults to config.",
    )
    parser.add_argument("--model", help="Model identifier; defaults depend on --agent.")
    parser.add_argument("--reasoning-effort", default=None)
    parser.add_argument("--codex-bin", default=None)
    parser.add_argument("--claude-bin", default=None)
    parser.add_argument("--timeout-seconds", type=int, default=900)
    parser.add_argument("--dry-run", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    skill_path = Path(args.skill)
    if not skill_path.is_absolute():
        skill_path = (REPO_ROOT / skill_path).resolve()
    if not skill_path.exists():
        print(f"skill file not found: {skill_path}", file=sys.stderr)
        return 2

    original_src, verified_src, default_stem = resolve_workspace_inputs(args)
    cfg = agent_config.load(args.config)
    agent = args.agent or cfg.agent(DEFAULT_AGENT)
    model = args.model or cfg.default_model(agent, DEFAULT_MODEL_CLAUDE if agent == AGENT_CLAUDE else DEFAULT_MODEL_CODEX)
    reasoning_effort = args.reasoning_effort or cfg.reasoning_effort(DEFAULT_REASONING_EFFORT)
    codex_bin = args.codex_bin or cfg.bin("codex", "codex")
    claude_bin = args.claude_bin or cfg.bin("claude", "claude")
    stem = args.workspace_name or default_stem
    timestamp = args.timestamp or timestamp_now()
    workspace = OUTPUT_ROOT / f"audit_{timestamp}_{stem}"
    logs_dir = workspace / "logs"
    audit_dir = workspace / "audit"
    original_dir = workspace / "original"
    verified_dir = workspace / "verified"
    for d in (logs_dir, audit_dir, original_dir, verified_dir):
        d.mkdir(parents=True, exist_ok=True)

    original_copy = original_dir / original_src.name
    verified_copy = verified_dir / verified_src.name
    shutil.copy2(original_src, original_copy)
    shutil.copy2(verified_src, verified_copy)

    findings_json = audit_dir / "findings.json"
    findings_md = audit_dir / "findings.md"
    final_result_md = logs_dir / "final_result.md"

    run_label = timestamp_now()
    prompt_path = logs_dir / f"agent_prompt_{run_label}.txt"
    stderr_path = logs_dir / f"agent_stderr_{run_label}.log"
    last_message_path = logs_dir / f"agent_last_message_{run_label}.txt"
    if agent == AGENT_CODEX:
        stdout_path = logs_dir / f"agent_stdout_{run_label}.jsonl"
    else:
        stdout_path = logs_dir / f"agent_stdout_{run_label}.log"

    emit(f"agent={agent}")
    emit(f"workspace={workspace}")
    emit(f"original={original_copy}")
    emit(f"verified={verified_copy}")

    start = time.time()
    start_iso = iso_now()
    exit_code = 0
    usage: dict[str, int] | None = None
    audit_script_exit: int | None = None
    openjml_exit: int | None = None
    judgment = "Audit was not fully executed."

    # Deterministic detection always runs (even in dry-run) so the findings
    # file exists for downstream consumers.
    audit_script_exit = run_audit_script(verified_copy, original_copy, findings_json, logs_dir)
    openjml_exit = run_openjml_cross_check(verified_copy, logs_dir)

    prompt = build_prompt(
        skill_path,
        workspace,
        original_copy,
        verified_copy,
        findings_json,
        findings_md,
        final_result_md,
        openjml_exit,
        audit_script_exit,
    )
    prompt_path.write_text(prompt, encoding="utf-8")

    if args.dry_run:
        stdout_path.write_text("", encoding="utf-8")
        stderr_path.write_text("", encoding="utf-8")
        last_message_path.write_text("Dry run: agent was not invoked.\n", encoding="utf-8")
        (logs_dir / "reasoning.md").write_text(
            "# Audit Reasoning\n\nDry run prepared the audit workspace; agent was not invoked.\n",
            encoding="utf-8",
        )
        (logs_dir / "issues.md").write_text(
            "# Audit Issues\n\nDry run only; agent did not render findings.\n",
            encoding="utf-8",
        )
        status = "Fail"
        judgment = "Dry run only; audit did not render a verdict."
    else:
        # The agent always runs: it is the only semantic review layer. audit_jml.py
        # is purely syntactic (regex + textual contract-clause diff), so a clean
        # deterministic result is NOT sufficient for a justified audit report.
        # Never short-circuit it away.
        agent_env = build_agent_env(logs_dir)
        if agent == AGENT_CODEX:
            exit_code = run_codex_agent(
                codex_bin=codex_bin,
                model=model,
                reasoning_effort=reasoning_effort,
                timeout_seconds=args.timeout_seconds,
                prompt=prompt,
                stdout_path=stdout_path,
                stderr_path=stderr_path,
                last_message_path=last_message_path,
                env=agent_env,
            )
            filter_stderr(stderr_path)
            usage = agent_metrics.parse_usage(agent, stdout_path)
        else:
            exit_code = run_claude_agent(
                claude_bin=claude_bin,
                model=model,
                reasoning_effort=reasoning_effort,
                timeout_seconds=args.timeout_seconds,
                prompt=prompt,
                stdout_path=stdout_path,
                stderr_path=stderr_path,
                last_message_path=last_message_path,
                env=agent_env,
            )
            filter_stderr(stderr_path)
            usage = agent_metrics.parse_usage(agent, stdout_path)

        if not findings_md.exists():
            (audit_dir / "findings.md").write_text(
                "# Audit Findings\n\nAgent did not render findings.md.\n",
                encoding="utf-8",
            )
        if not (logs_dir / "reasoning.md").exists():
            (logs_dir / "reasoning.md").write_text(
                "# Audit Reasoning\n\nAgent did not render reasoning.md.\n",
                encoding="utf-8",
            )
        if not (logs_dir / "issues.md").exists():
            (logs_dir / "issues.md").write_text(
                "# Audit Issues\n\nNo issues recorded.\n",
                encoding="utf-8",
            )
        if not final_result_md.exists():
            final_result_md.write_text(
                "# Audit Final Result\n\n- Audit verdict: NotVerified\n"
                "- Detail: agent did not author final_result.md\n",
                encoding="utf-8",
            )

        verdict = read_audit_verdict(final_result_md)
        decisive = verdict in {"VerifiedClean", "VerifiedWithWarnings", "NotVerified"}
        success = exit_code == 0 and decisive and verdict != "NotVerified"
        status = "Success" if success else "Fail"
        if not decisive:
            judgment = "Audit did not write a recognized verdict."
        elif verdict == "NotVerified":
            judgment = "Audit verdict: NotVerified — anti-cheating violations remain."
        elif verdict == "VerifiedWithWarnings":
            judgment = "Audit verdict: VerifiedWithWarnings — only warning-severity items."
        else:
            judgment = "Audit verdict: VerifiedClean — no remaining anti-cheating violations."

    error_findings, warning_findings = count_findings(findings_json)
    audit_verdict = read_audit_verdict(final_result_md)

    end_iso = iso_now()
    write_metrics(
        logs_dir / "metrics.md",
        agent=agent,
        status=status,
        dry_run=args.dry_run,
        exit_code=exit_code,
        start_iso=start_iso,
        end_iso=end_iso,
        wall_seconds=time.time() - start,
        model=model,
        reasoning_effort=reasoning_effort,
        original_java=original_copy,
        verified_java=verified_copy,
        prompt_path=prompt_path,
        stdout_path=stdout_path,
        stderr_path=stderr_path,
        last_message_path=last_message_path,
        usage=usage,
        audit_script_exit=audit_script_exit,
        openjml_exit=openjml_exit,
        error_findings=error_findings,
        warning_findings=warning_findings,
        audit_verdict=audit_verdict,
        judgment=judgment,
    )
    print(str(workspace))
    return 0 if status == "Success" else 1


if __name__ == "__main__":
    raise SystemExit(main())

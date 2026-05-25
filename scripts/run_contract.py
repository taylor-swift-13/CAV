#!/usr/bin/env python3
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
import agent_loop
import agent_config
import agent_metrics


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SKILL = REPO_ROOT / "skills" / "contract" / "SKILL.md"
OUTPUT_ROOT = REPO_ROOT / "output"
INPUT_ROOT = REPO_ROOT / "input"
DEFAULT_MODEL = "gpt-5.4"
DEFAULT_CLAUDE_MODEL = "sonnet"
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


def ensure_parent(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


def emit(message: str) -> None:
    print(f"[contract] {message}", flush=True)


def build_codex_env(logs_dir: Path) -> dict[str, str]:
    env = os.environ.copy()
    for name, dirname in {
        "XDG_CACHE_HOME": ".codex_cache",
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


def filter_stderr(path: Path) -> None:
    if not path.exists():
        return
    kept = []
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        if any(pattern in line for pattern in NOISE_PATTERNS):
            continue
        kept.append(line)
    path.write_text("\n".join(kept) + ("\n" if kept else ""), encoding="utf-8")


def build_prompt(
    skill: Path,
    raw: Path,
    function_name: str,
    workspace: Path,
    target_java: Path,
    attempt: int,
    restart_context: str | None,
) -> str:
    logs = workspace / "logs"
    if attempt <= 1 and not restart_context:
        intro = "Start the normal Java/OpenJML contract workflow for this task."
    elif restart_context:
        intro = (
            "Re-entry: a downstream check overturned a previous result. Read the "
            f"overturn section in `{logs / 'continue.md'}` and the cited findings "
            "first, then fix exactly that problem."
        )
    else:
        intro = (
            "Retry in the same workspace. Do not restart from scratch. Read the "
            f"existing logs (`{logs / 'issues.md'}`, `{logs / 'reasoning.md'}`, "
            f"`{logs / 'wellformed_classification.md'}`, latest `codex_last_message_*`) "
            "and continue from the current blocker."
        )
    return f"""Use this skill as the complete workflow:
{skill}

{intro}

Inputs:
- Raw markdown: `{raw}`
- Target function or class: `{function_name}`
- Workspace: `{workspace}`
- Output Java: `{target_java}`

Iteration rules:
- Keep iterating in this same workspace until the spec passes the
  well-formedness gate and anti-cheating scan, or the time budget is exhausted.
- On every round, before editing, append a fresh section to `{logs / 'continue.md'}`
  (never overwrite): why the previous round did not finish, the concrete blocker
  now, the next step, and the plan, citing concrete evidence (file:line, the
  OpenJML / well-formedness message, the spec snippet).
- At the end of each round, write `{logs / 'summary.md'}`: what you did, the
  current spec state, and where you are stuck (used to resume on restart).
- Preserve correct work; only change what the current blocker needs.

Repository rules:
- This is Java/OpenJML, not C/Coq Verify.
- Before writing output, search `/home/yangfp/CAV-JAVA/experiences/end-end` for completed examples and reuse relevant patterns.
- Record any relevant completed example path in `{logs / 'reasoning.md'}`.
- The spec must be well-formed: no `\\num_of`/`\\sum`/`\\product` or any
  `NOT IMPLEMENTED` feature. Use a `pure` recursive helper for count/sum results.
- Write only Java/JML contract output in the contract stage.
- Do not use assume, axiom, skipesc, nowarn, native, or unchecked helpers.
- Do not record experience yourself; experience is consolidated once at the end
  of the flow by a dedicated unit.
- Write logs under `{logs}`.
"""


def write_placeholder_logs(logs_dir: Path, stage: str, detail: str) -> None:
    (logs_dir / "reasoning.md").write_text(f"# {stage.title()} Reasoning\n\n{detail}\n", encoding="utf-8")
    (logs_dir / "issues.md").write_text(f"# {stage.title()} Issues\n\nNo issues recorded yet.\n", encoding="utf-8")


def write_metrics(
    path: Path,
    *,
    status: str,
    attempts: int,
    last_codex_exit: int,
    start_iso: str,
    end_iso: str,
    wall_seconds: float,
    model: str,
    reasoning_effort: str,
    prompt_path: Path,
    stdout_jsonl: Path,
    stderr_log: Path,
    last_message_path: Path,
    target_java: Path,
    usage: dict[str, int] | None,
    scanner_exit: int | None,
    wellformed_exit: int | None,
    dry_run: bool,
) -> None:
    lines = [
        "# Contract Metrics",
        "",
        f"- Stage: `contract`",
        f"- Status: `{status}`",
        f"- Dry run: `{str(dry_run).lower()}`",
        f"- Attempts: `{attempts}`",
        f"- Last Codex exit code: `{last_codex_exit}`",
        f"- Start time: `{start_iso}`",
        f"- End time: `{end_iso}`",
        f"- Wall-clock time (seconds): `{wall_seconds:.2f}`",
        f"- Model: `{model}`",
        f"- Reasoning effort: `{reasoning_effort}`",
        f"- Output Java: `{target_java}`",
        f"- Anti-cheating scanner exit code: `{scanner_exit if scanner_exit is not None else 'not_run'}`",
        f"- Spec well-formedness gate exit code: `{wellformed_exit if wellformed_exit is not None else 'not_run'}`",
        f"- Prompt file: `{prompt_path}`",
        f"- Codex stdout JSONL: `{stdout_jsonl}`",
        f"- Codex stderr log: `{stderr_log}`",
        f"- Codex last message: `{last_message_path}`",
    ]
    lines.extend(agent_metrics.usage_lines(
        usage, prompt_path=prompt_path, last_message_path=last_message_path))
    lines.extend(["- Experience: consolidated at end of flow", f"Final Result: {status}"])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run Codex for Java/OpenJML contract generation.")
    parser.add_argument("raw_md", help="Path to raw markdown task.")
    parser.add_argument("--function-name", required=True, help="Target method or class name.")
    parser.add_argument("--skill", default=str(DEFAULT_SKILL), help="Path to contract skill.")
    parser.add_argument("--workspace-name", help="Workspace/output stem. Defaults to raw filename stem.")
    parser.add_argument("--timestamp", help="Explicit timestamp. Defaults to current local time.")
    parser.add_argument("--config", default=None, help="Path to agents.json config.")
    parser.add_argument("--agent", choices=["codex", "claude"], default=None)
    parser.add_argument("--model", default=None,
                        help="Model. Defaults to gpt-5.4 (codex) or sonnet (claude).")
    parser.add_argument("--reasoning-effort", default=None)
    parser.add_argument("--codex-bin", default=None)
    parser.add_argument("--claude-bin", default=None)
    parser.add_argument("--timeout-seconds", type=int, default=1800,
                        help="Total wall-clock budget for this contract invocation.")
    parser.add_argument("--restart-from", help="Path to a critic findings file injected as restart context.")
    parser.add_argument("--resume-workspace", help="Reuse an existing contract workspace instead of creating one.")
    parser.add_argument("--dry-run", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    raw_path = Path(args.raw_md)
    if not raw_path.is_absolute():
        raw_path = (REPO_ROOT / raw_path).resolve()
    skill_path = Path(args.skill)
    if not skill_path.is_absolute():
        skill_path = (REPO_ROOT / skill_path).resolve()
    if not raw_path.exists():
        print(f"raw markdown not found: {raw_path}", file=sys.stderr)
        return 2
    if not skill_path.exists():
        print(f"skill file not found: {skill_path}", file=sys.stderr)
        return 2

    cfg = agent_config.load(args.config)
    agent = args.agent or cfg.agent("codex")
    model = args.model or cfg.solver_model(agent, DEFAULT_CLAUDE_MODEL if agent == "claude" else DEFAULT_MODEL)
    reasoning_effort = args.reasoning_effort or cfg.reasoning_effort(DEFAULT_REASONING_EFFORT)
    codex_bin = args.codex_bin or cfg.bin("codex", "codex")
    claude_bin = args.claude_bin or cfg.bin("claude", "claude")

    stem = args.workspace_name or raw_path.stem
    timestamp = args.timestamp or timestamp_now()
    if args.resume_workspace:
        workspace = Path(args.resume_workspace).resolve()
    else:
        workspace = OUTPUT_ROOT / f"contract_{timestamp}_{stem}"
    logs_dir = workspace / "logs"
    raw_dir = workspace / "raw"
    INPUT_ROOT.mkdir(parents=True, exist_ok=True)
    logs_dir.mkdir(parents=True, exist_ok=True)
    raw_dir.mkdir(parents=True, exist_ok=True)
    shutil.copy2(raw_path, raw_dir / raw_path.name)

    target_java = INPUT_ROOT / f"{stem}.java"
    restart_context = None
    if args.restart_from:
        rf = Path(args.restart_from)
        if rf.exists():
            restart_context = (
                f"Findings injected from `{rf}`:\n\n"
                + rf.read_text(encoding="utf-8", errors="replace")
            )

    emit(f"workspace={workspace}")
    emit(f"target_java={target_java}")

    start = time.time()
    start_iso = iso_now()

    # Track per-round artifacts so write_metrics points at the last round.
    state: dict[str, object] = {
        "scanner_exit": None,
        "wellformed_exit": None,
        "last_codex_exit": 0,
        "prompt_path": None,
        "stdout_jsonl": None,
        "stderr_log": None,
        "last_message_path": None,
        "usage": None,  # accumulated across all rounds
    }

    if args.dry_run:
        run_label = timestamp_now()
        state["prompt_path"] = logs_dir / f"codex_prompt_{run_label}.txt"
        state["stdout_jsonl"] = logs_dir / f"codex_stdout_{run_label}.jsonl"
        state["stderr_log"] = logs_dir / f"codex_stderr_{run_label}.log"
        state["last_message_path"] = logs_dir / f"codex_last_message_{run_label}.txt"
        state["prompt_path"].write_text(
            build_prompt(skill_path, raw_path, args.function_name, workspace, target_java, 1, restart_context),
            encoding="utf-8",
        )
        write_placeholder_logs(logs_dir, "contract", "Dry run prepared the workspace and prompt; Codex was not invoked.")
        state["last_message_path"].write_text("Dry run: Codex was not invoked.\n", encoding="utf-8")
        state["stdout_jsonl"].write_text("", encoding="utf-8")
        state["stderr_log"].write_text("", encoding="utf-8")
        status, attempts = "Success", 0
    else:
        codex_env = build_codex_env(logs_dir)

        def attempt_fn(attempt: int, rc: str | None, round_timeout: int) -> tuple[str, str]:
            run_label = timestamp_now()
            prompt_path = logs_dir / f"codex_prompt_{run_label}.txt"
            stdout_jsonl = logs_dir / f"codex_stdout_{run_label}.jsonl"
            stderr_log = logs_dir / f"codex_stderr_{run_label}.log"
            last_message_path = logs_dir / f"codex_last_message_{run_label}.txt"
            state.update(prompt_path=prompt_path, stdout_jsonl=stdout_jsonl,
                         stderr_log=stderr_log, last_message_path=last_message_path)
            prompt = build_prompt(skill_path, raw_path, args.function_name, workspace, target_java, attempt, rc)
            prompt_path.write_text(prompt, encoding="utf-8")

            exit_code, timed_out = agent_loop.run_agent_round(
                agent=agent, codex_bin=codex_bin, claude_bin=claude_bin,
                model=model, reasoning_effort=reasoning_effort, prompt=prompt,
                stdout_jsonl=stdout_jsonl, stderr_log=stderr_log,
                last_message_path=last_message_path, env=codex_env,
                timeout_seconds=round_timeout,
            )
            state["last_codex_exit"] = exit_code
            state["usage"] = agent_metrics.add_usage(
                state["usage"], agent_metrics.parse_usage(agent, stdout_jsonl))
            if timed_out:
                return agent_loop.STATUS_TIMEOUT, "codex round timed out"

            scanner_exit = wellformed_exit = None
            if target_java.exists():
                scanner = subprocess.run(
                    [sys.executable, str(REPO_ROOT / "scripts" / "check_jml_cheating.py"), str(target_java)],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, cwd=REPO_ROOT,
                )
                scanner_exit = scanner.returncode
                (logs_dir / "cheating_scan_stdout.log").write_text(scanner.stdout, encoding="utf-8")
                (logs_dir / "cheating_scan_stderr.log").write_text(scanner.stderr, encoding="utf-8")
                # Well-formedness gate: spec must parse/type-check and use only
                # verifier-supported features. Undischarged VCs are tolerated
                # (that is verify's job); NOT IMPLEMENTED / \num_of / \sum /
                # \product and parse/type errors are fatal here.
                if scanner_exit == 0:
                    wf = subprocess.run(
                        [sys.executable, str(REPO_ROOT / "scripts" / "check_spec_wellformed.py"),
                         str(target_java), "--log-dir", str(logs_dir)],
                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, cwd=REPO_ROOT,
                    )
                    wellformed_exit = wf.returncode
            state["scanner_exit"], state["wellformed_exit"] = scanner_exit, wellformed_exit

            if exit_code == 0 and target_java.exists() and scanner_exit == 0 and wellformed_exit == 0:
                return agent_loop.STATUS_SUCCESS, "contract well-formed and clean"
            reason = (
                f"codex_exit={exit_code} java_exists={target_java.exists()} "
                f"scanner_exit={scanner_exit} wellformed_exit={wellformed_exit}"
            )
            return agent_loop.STATUS_FAIL, reason

        result = agent_loop.run(
            logs_dir=logs_dir, attempt_fn=attempt_fn,
            budget_seconds=args.timeout_seconds, restart_context=restart_context,
            emit=lambda m: emit(f"loop {m}"),
        )
        status, attempts = result.status, result.attempts
        if not (logs_dir / "issues.md").exists():
            detail = "No issues recorded by Codex." if status == "Success" else "Contract did not complete successfully."
            (logs_dir / "issues.md").write_text(f"# Contract Issues\n\n{detail}\n", encoding="utf-8")
        if not (logs_dir / "reasoning.md").exists():
            (logs_dir / "reasoning.md").write_text("# Contract Reasoning\n\nNo reasoning log was produced.\n", encoding="utf-8")

    end_iso = iso_now()
    usage = state["usage"]
    write_metrics(
        logs_dir / "metrics.md",
        status=status,
        attempts=attempts,
        last_codex_exit=int(state["last_codex_exit"]),
        start_iso=start_iso,
        end_iso=end_iso,
        wall_seconds=time.time() - start,
        model=model,
        reasoning_effort=reasoning_effort,
        prompt_path=state["prompt_path"],
        stdout_jsonl=state["stdout_jsonl"],
        stderr_log=state["stderr_log"],
        last_message_path=state["last_message_path"],
        target_java=target_java,
        usage=usage,
        scanner_exit=state["scanner_exit"],
        wellformed_exit=state["wellformed_exit"],
        dry_run=args.dry_run,
    )
    print(str(workspace))
    return 0 if status == "Success" else 1


if __name__ == "__main__":
    raise SystemExit(main())

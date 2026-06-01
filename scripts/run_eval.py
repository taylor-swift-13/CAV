#!/usr/bin/env python3
"""Run the eval stage with codex or claude-code as the backend agent.

Eval has a single job: decide whether the JML spec attached to an
implementation correctly characterizes that implementation's behavior. It
treats the spec as an executable predicate (spec-test):

  generate concrete cases -> mechanically substitute each case into every spec
  clause -> only clauses that cannot be decided mechanically go to an
  LLM-as-judge -> aggregate a `Spec verdict:` (Correct / Buggy / Inconclusive).

Eval does NOT check well-formedness and does NOT invoke `openjml -esc`. The
contract stage's success gate already guarantees the spec parses, type-checks,
is free of `NOT IMPLEMENTED` and the unsupported aggregate quantifiers, and
passes the anti-cheating scan (see scripts/check_spec_wellformed.py wired into
scripts/run_contract.py). Deductive proof is the verify/audit stage's
job. So by the time eval runs, the spec is already well-formed and eval only
has to test its semantics.

This runner replaces the older scripts/run_codex_eval.py, scripts/run_spec_test.py,
and the earlier harness mode of this script.
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
DEFAULT_SKILL = REPO_ROOT / "skills" / "eval" / "SKILL.md"
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
    print(f"[eval] {message}", flush=True)


def class_name_from_stem(stem: str) -> str:
    return "".join(part[:1].upper() + part[1:] for part in stem.replace("-", "_").split("_") if part)


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


def build_prompt_spec_test(
    skill: Path,
    impl_java: Path,
    class_name: str,
    method_name: str,
    workspace: Path,
    num_positive: int,
    num_negative: int,
) -> str:
    cases_dir = workspace / "cases"
    eval_dir = workspace / "evaluation"
    logs_dir = workspace / "logs"
    return f"""Use this skill as the complete workflow:
{skill}

Inputs:
- Implementation/spec Java: `{impl_java}`
- Target class: `{class_name}`
- Target method: `{method_name}`
- Workspace: `{workspace}`
- Cases directory: `{cases_dir}`
- Evaluation directory: `{eval_dir}`
- Logs directory: `{logs_dir}`

Simple flow: GENERATE cases -> TEST each mechanically -> only what cannot be
tested mechanically goes to the JUDGE. No elaborate tier bookkeeping.

Rules:
- This eval stage is independent from contract, verify, and audit.
- The spec is already well-formed (the contract stage guarantees it parses,
  type-checks, and is free of `NOT IMPLEMENTED` / unsupported aggregate
  quantifiers). Do NOT re-check well-formedness and do NOT invoke `openjml -esc`.
- Do not modify `{impl_java}`.
- GENERATE exactly {num_positive} positive and {num_negative} negative concrete cases in
  `{cases_dir / 'cases.json'}` (schema per the skill). Positive `result` /
  `post_state` come from running the implementation. Choose cases adversarially:
  positives must cover EVERY branch / input partition (e.g. both `a >= b` and
  `a < b`) and stress each `ensures` clause, so a one-branch spec bug is not
  missed because no case hit that branch.
- TEST: for each case, substitute its values into every spec clause and compute
  the boolean (enumerate bounded quantifiers over the case's concrete range).
  A clause that cannot be decided mechanically (unbounded quantifier, model
  function, etc.) is marked `needs_judge`; JUDGE only those.
- Write ONE results file `{eval_dir / 'evaluation.json'}`:
  ```json
  {{"cases": [
     {{"id": "pos01", "verdict": "pass|fail|needs_judge",
       "clauses": [{{"clause": "...", "substituted": "5 == 5", "evaluated": true}}],
       "judge": {{"verdict": "pass|fail|inconclusive", "reason": "..."}}  // only if needs_judge
     }}
  ]}}
  ```
  Every clause record needs `substituted` + `evaluated`; `judge` is present only
  for `needs_judge` cases.
- Aggregate into `{logs_dir / 'final_result.md'}` with one of:
  `Spec verdict: Correct` (all positives pass, all negatives fail),
  `Spec verdict: Buggy` (a positive failed or a negative passed),
  `Spec verdict: Inconclusive` (a judged clause stays inconclusive).
- After the spec-test, run the same LLM judge as the C eval flow. Judge whether
  the spec is sound and complete for the intended method behavior:
  * Soundness: every input/output of the correct program satisfies the spec.
  * Positive coverage: all positive cases satisfy the spec.
  * Parameter coverage: all input, output, and necessary post-state parameters
    are constrained by the spec.
  * Path coverage: all method paths / branches are covered.
  * Negative rejection: all negative cases are rejected by the spec.
  * Completeness: any implementation satisfying the spec is a correct solution
    to this problem.
  Write `Judge verdict: Pass` only if all six items pass. Otherwise write
  `Judge verdict: Fail`; use `Judge verdict: Inconclusive` if undecidable.
- Do not use assume, axiom, skipesc, nowarn, native, reflection, or
  unreachable-path tricks.
- Write `test_reasoning.md`, `issues.md`, `final_result.md`, `metrics.md` under
  `{logs_dir}`; `metrics.md` ends with `Final Result: Success` or `Fail`.
"""


def append_issue(logs_dir: Path, title: str, detail: str) -> None:
    issues = logs_dir / "issues.md"
    existing = issues.read_text(encoding="utf-8") if issues.exists() else "# Eval Issues\n\n"
    issues.write_text(existing.rstrip() + f"\n\n## {title}\n\n{detail}\n", encoding="utf-8")


def write_placeholder_logs(logs_dir: Path, detail: str) -> None:
    (logs_dir / "test_reasoning.md").write_text(f"# Eval Reasoning\n\n{detail}\n", encoding="utf-8")
    (logs_dir / "issues.md").write_text("# Eval Issues\n\nNo issues recorded yet.\n", encoding="utf-8")


def count_spec_test_cases(cases_json: Path) -> tuple[int, int, str | None]:
    if not cases_json.exists():
        return 0, 0, f"cases.json not found at {cases_json}"
    try:
        data = json.loads(cases_json.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        return 0, 0, f"cases.json is not valid JSON: {exc}"
    pos = data.get("positive") if isinstance(data, dict) else None
    neg = data.get("negative") if isinstance(data, dict) else None
    p = len(pos) if isinstance(pos, list) else 0
    n = len(neg) if isinstance(neg, list) else 0
    return p, n, None


def read_final_result_value(final_result: Path, marker: str) -> str | None:
    if not final_result.exists():
        return None
    for raw in final_result.read_text(encoding="utf-8", errors="replace").splitlines():
        # Tolerate markdown decoration: "## Spec verdict:", "- **Judge verdict:**", etc.
        line = raw.strip().lstrip("#*->` ").strip()
        if line.lower().startswith(marker.lower()):
            return line.split(":", 1)[1].strip().strip("*`").strip()
    return None


def read_spec_verdict(final_result: Path) -> str | None:
    return read_final_result_value(final_result, "Spec verdict:")


def read_judge_verdict(final_result: Path) -> str | None:
    return read_final_result_value(final_result, "Judge verdict:")


def validate_spec_test_artifacts(cases_json: Path, evaluation_json: Path, num_pos: int, num_neg: int) -> tuple[bool, str]:
    if not cases_json.exists():
        return False, f"cases.json not found at {cases_json}"
    if not evaluation_json.exists():
        return False, f"evaluation.json not found at {evaluation_json}"
    try:
        cases_doc = json.loads(cases_json.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        return False, f"cases.json is not valid JSON: {exc}"
    try:
        eval_doc = json.loads(evaluation_json.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        return False, f"evaluation.json is not valid JSON: {exc}"

    positives = cases_doc.get("positive") if isinstance(cases_doc, dict) else None
    negatives = cases_doc.get("negative") if isinstance(cases_doc, dict) else None
    if not isinstance(positives, list) or len(positives) != num_pos:
        return False, f"positive case count mismatch: {len(positives) if isinstance(positives, list) else 'missing'} != {num_pos}"
    if not isinstance(negatives, list) or len(negatives) != num_neg:
        return False, f"negative case count mismatch: {len(negatives) if isinstance(negatives, list) else 'missing'} != {num_neg}"

    positive_ids = {str(c.get("id")) for c in positives if isinstance(c, dict) and c.get("id") is not None}
    negative_ids = {str(c.get("id")) for c in negatives if isinstance(c, dict) and c.get("id") is not None}
    expected_ids = positive_ids | negative_ids
    eval_cases = eval_doc.get("cases") if isinstance(eval_doc, dict) else None
    if not isinstance(eval_cases, list):
        return False, "evaluation cases missing"
    evaluated_ids = {str(c.get("id")) for c in eval_cases if isinstance(c, dict) and c.get("id") is not None}
    missing = sorted(expected_ids - evaluated_ids)
    if missing:
        return False, "evaluation missing cases: " + ",".join(missing)

    def effective_verdict(case: dict) -> str | None:
        verdict = case.get("verdict")
        if verdict != "needs_judge":
            return verdict
        judge = case.get("judge")
        if not isinstance(judge, dict):
            return None
        return judge.get("verdict")

    verdict_by_id = {
        str(c.get("id")): effective_verdict(c)
        for c in eval_cases
        if isinstance(c, dict) and c.get("id") is not None
    }
    unresolved = sorted(cid for cid in expected_ids if verdict_by_id.get(cid) not in {"pass", "fail"})
    if unresolved:
        return False, "evaluation has unresolved cases: " + ",".join(unresolved)
    positive_failures = sorted(cid for cid in positive_ids if verdict_by_id.get(cid) != "pass")
    negative_failures = sorted(cid for cid in negative_ids if verdict_by_id.get(cid) != "fail")
    if positive_failures:
        return False, "positive cases not pass: " + ",".join(positive_failures)
    if negative_failures:
        return False, "negative cases not rejected: " + ",".join(negative_failures)
    return True, "spec-test artifacts ok"


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
    impl_java: Path,
    prompt_path: Path,
    stdout_path: Path,
    stderr_path: Path,
    last_message_path: Path,
    usage: dict[str, int] | None,
    positive_count: int,
    negative_count: int,
    extras: list[tuple[str, str]],
    judgment: str,
) -> None:
    lines = [
        "# Eval Metrics",
        "",
        f"- Stage: `eval`",
        f"- Mode: `spec-test`",
        f"- Agent: `{agent}`",
        f"- Status: `{status}`",
        f"- Dry run: `{str(dry_run).lower()}`",
        f"- Agent exit code: `{exit_code}`",
        f"- Start time: `{start_iso}`",
        f"- End time: `{end_iso}`",
        f"- Wall-clock time (seconds): `{wall_seconds:.2f}`",
        f"- Model: `{model}`",
        f"- Reasoning effort: `{reasoning_effort}`",
        f"- Implementation Java: `{impl_java}`",
        f"- Positive cases found: `{positive_count}`",
        f"- Negative cases found: `{negative_count}`",
    ]
    for label, value in extras:
        lines.append(f"- {label}: `{value}`")
    lines.extend(
        [
            f"- Final judgment: `{judgment}`",
            f"- Prompt file: `{prompt_path}`",
            f"- Agent stdout: `{stdout_path}`",
            f"- Agent stderr: `{stderr_path}`",
            f"- Agent last message: `{last_message_path}`",
        ]
    )
    lines.extend(agent_metrics.usage_lines(
        usage, prompt_path=prompt_path, last_message_path=last_message_path))
    lines.extend(["- Experience: consolidated at end of flow", f"Final Result: {status}"])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run eval (spec-test) with codex or claude-code.")
    parser.add_argument("impl_java", help="Path to implementation/spec Java file.")
    parser.add_argument("--class-name", help="Target class name. Defaults to PascalCase filename stem.")
    parser.add_argument("--method-name", help="Target method name. Defaults to filename stem.")
    parser.add_argument("--skill", default=str(DEFAULT_SKILL), help="Path to eval skill.")
    parser.add_argument("--workspace-name", help="Workspace/output stem. Defaults to input filename stem.")
    parser.add_argument("--timestamp", help="Explicit timestamp. Defaults to current local time.")
    parser.add_argument("--config", default=None, help="Path to agents.json config.")
    parser.add_argument(
        "--agent",
        choices=[AGENT_CODEX, AGENT_CLAUDE],
        default=None,
        help="Which CLI to drive: 'codex' or 'claude'. Defaults to config.",
    )
    parser.add_argument("--num-positive", type=int, default=None,
                        help="Number of positive cases (default: config or 4).")
    parser.add_argument("--num-negative", type=int, default=None,
                        help="Number of negative cases (default: config or 4).")
    parser.add_argument("--model", help="Model identifier; defaults depend on --agent.")
    parser.add_argument("--reasoning-effort", default=None)
    parser.add_argument("--codex-bin", default=None)
    parser.add_argument("--claude-bin", default=None)
    parser.add_argument("--timeout-seconds", type=int, default=1800)
    parser.add_argument("--dry-run", action="store_true")
    return parser


def invoke_eval_agent(
    *, agent: str, model: str, reasoning_effort: str, timeout_seconds: int,
    prompt: str, logs_dir: Path, run_label: str, codex_bin: str, claude_bin: str,
) -> tuple[int, dict[str, int] | None, Path, Path, Path, Path]:
    """Run one eval agent session. Returns (exit, usage, stdout, prompt, stderr, last_message)."""
    env = build_agent_env(logs_dir)
    prompt_path = logs_dir / f"agent_prompt_{run_label}.txt"
    prompt_path.write_text(prompt, encoding="utf-8")
    stderr_path = logs_dir / f"agent_stderr_{run_label}.log"
    last_message_path = logs_dir / f"agent_last_message_{run_label}.txt"
    if agent == AGENT_CODEX:
        stdout_path = logs_dir / f"agent_stdout_{run_label}.jsonl"
        rc = run_codex_agent(
            codex_bin=codex_bin, model=model, reasoning_effort=reasoning_effort,
            timeout_seconds=timeout_seconds, prompt=prompt, stdout_path=stdout_path,
            stderr_path=stderr_path, last_message_path=last_message_path, env=env,
        )
        filter_stderr(stderr_path)
        usage = agent_metrics.parse_usage(agent, stdout_path)
    else:
        stdout_path = logs_dir / f"agent_stdout_{run_label}.log"
        rc = run_claude_agent(
            claude_bin=claude_bin, model=model, reasoning_effort=reasoning_effort,
            timeout_seconds=timeout_seconds, prompt=prompt, stdout_path=stdout_path,
            stderr_path=stderr_path, last_message_path=last_message_path, env=env,
        )
        filter_stderr(stderr_path)
        usage = agent_metrics.parse_usage(agent, stdout_path)
    return rc, usage, stdout_path, prompt_path, stderr_path, last_message_path


def main() -> int:
    args = build_parser().parse_args()
    impl_java = Path(args.impl_java)
    if not impl_java.is_absolute():
        impl_java = (REPO_ROOT / impl_java).resolve()
    skill_path = Path(args.skill)
    if not skill_path.is_absolute():
        skill_path = (REPO_ROOT / skill_path).resolve()
    if not impl_java.exists():
        print(f"implementation Java not found: {impl_java}", file=sys.stderr)
        return 2
    if impl_java.suffix != ".java":
        print(f"implementation file must be .java: {impl_java}", file=sys.stderr)
        return 2
    if not skill_path.exists():
        print(f"skill file not found: {skill_path}", file=sys.stderr)
        return 2

    cfg = agent_config.load(args.config)
    agent = args.agent or cfg.agent(DEFAULT_AGENT)
    model = args.model or cfg.default_model(agent, DEFAULT_MODEL_CLAUDE if agent == AGENT_CLAUDE else DEFAULT_MODEL_CODEX)
    reasoning_effort = args.reasoning_effort or cfg.reasoning_effort(DEFAULT_REASONING_EFFORT)
    codex_bin = args.codex_bin or cfg.bin("codex", "codex")
    claude_bin = args.claude_bin or cfg.bin("claude", "claude")

    stem = args.workspace_name or impl_java.stem
    timestamp = args.timestamp or timestamp_now()
    class_name = args.class_name or class_name_from_stem(stem)
    method_name = args.method_name or stem
    workspace = OUTPUT_ROOT / f"eval_{timestamp}_{stem}"
    logs_dir = workspace / "logs"
    original_dir = workspace / "original"
    logs_dir.mkdir(parents=True, exist_ok=True)
    original_dir.mkdir(parents=True, exist_ok=True)
    shutil.copy2(impl_java, original_dir / impl_java.name)

    run_label = timestamp_now()
    prompt_path = logs_dir / f"agent_prompt_{run_label}.txt"
    stderr_path = logs_dir / f"agent_stderr_{run_label}.log"
    last_message_path = logs_dir / f"agent_last_message_{run_label}.txt"

    cases_dir = workspace / "cases"
    eval_dir = workspace / "evaluation"
    cases_dir.mkdir(parents=True, exist_ok=True)
    eval_dir.mkdir(parents=True, exist_ok=True)

    num_pos = args.num_positive if args.num_positive is not None else cfg.eval_num("num_positive", 4)
    num_neg = args.num_negative if args.num_negative is not None else cfg.eval_num("num_negative", 4)

    emit(f"agent={agent}")
    emit(f"workspace={workspace}")
    emit(f"impl_java={impl_java}")

    start = time.time()
    start_iso = iso_now()
    exit_code = 0
    usage: dict[str, int] | None = None
    judgment = "Eval was not fully executed."

    stdout_path = logs_dir / (f"agent_stdout_{run_label}.jsonl" if agent == AGENT_CODEX
                              else f"agent_stdout_{run_label}.log")

    prompt = build_prompt_spec_test(skill_path, impl_java, class_name, method_name,
                                    workspace, num_pos, num_neg)

    if args.dry_run:
        prompt_path.write_text(prompt, encoding="utf-8")
        stdout_path.write_text("", encoding="utf-8")
        stderr_path.write_text("", encoding="utf-8")
        last_message_path.write_text("Dry run: agent was not invoked.\n", encoding="utf-8")
        write_placeholder_logs(
            logs_dir,
            "Dry run prepared the eval workspace and prompt; agent was not invoked.",
        )
        status = "Fail"
        judgment = "Dry run only; eval did not complete."
        extras: list[tuple[str, str]] = []
    else:
        # One capable model does generate -> mechanically test -> judge only the
        # cases it cannot mechanically decide.
        exit_code, usage, stdout_path, prompt_path, stderr_path, last_message_path = invoke_eval_agent(
            agent=agent, model=model, reasoning_effort=reasoning_effort,
            timeout_seconds=args.timeout_seconds, prompt=prompt, logs_dir=logs_dir,
            run_label=timestamp_now(), codex_bin=codex_bin, claude_bin=claude_bin)
        emit(f"spec-test phase model={model} exit={exit_code}")

        cases_json = cases_dir / "cases.json"
        positive_count, negative_count, cases_err = count_spec_test_cases(cases_json)
        if cases_err:
            append_issue(logs_dir, "Cases parse error", cases_err)
        else:
            if positive_count != num_pos:
                append_issue(
                    logs_dir,
                    "Incomplete positive cases",
                    f"Expected exactly {num_pos} positive cases in `{cases_json}`, found `{positive_count}`.",
                )
            if negative_count != num_neg:
                append_issue(
                    logs_dir,
                    "Incomplete negative cases",
                    f"Expected exactly {num_neg} negative cases in `{cases_json}`, found `{negative_count}`.",
                )

        evaluation_json = eval_dir / "evaluation.json"
        evaluation_present = evaluation_json.exists()
        if not evaluation_present:
            append_issue(logs_dir, "Missing evaluation output", f"Expected `{evaluation_json}`.")
        artifacts_ok, artifacts_detail = validate_spec_test_artifacts(cases_json, evaluation_json, num_pos, num_neg)
        if not artifacts_ok:
            append_issue(logs_dir, "Spec-test artifact gate failed", artifacts_detail)

        spec_verdict = read_spec_verdict(logs_dir / "final_result.md")
        judge_verdict = read_judge_verdict(logs_dir / "final_result.md")
        fully_run = (
            exit_code == 0
            and artifacts_ok
            and spec_verdict == "Correct"
            and judge_verdict == "Pass"
        )
        status = "Success" if fully_run else "Fail"
        if fully_run:
            judgment = f"spec-test and judge passed: spec={spec_verdict}, judge={judge_verdict}."
        elif spec_verdict == "Inconclusive":
            judgment = "spec-test verdict is Inconclusive (a judged clause stayed undecided); treated as Fail."
        elif judge_verdict in {"Fail", "Inconclusive"}:
            judgment = f"judge verdict is {judge_verdict}; treated as Fail."
        elif spec_verdict == "Buggy":
            judgment = "spec-test verdict is Buggy; treated as Fail and should overturn the contract."
        elif exit_code != 0:
            judgment = f"Agent exited with non-zero status ({exit_code}); spec-test did not complete."
        else:
            judgment = "spec-test artifacts or judge verdict are incomplete; see issues.md."

        if not (logs_dir / "final_result.md").exists():
            (logs_dir / "final_result.md").write_text(
                "# Eval Final Result (spec-test mode)\n\n"
                "Spec verdict: Inconclusive\n"
                "Judge verdict: Inconclusive\n"
                "- Detail: agent did not author final_result.md\n",
                encoding="utf-8",
            )

        extras = [
            ("Evaluation file present", str(evaluation_present).lower()),
            ("Artifact gate", artifacts_detail),
            ("Spec verdict", spec_verdict if spec_verdict else "unset"),
            ("Judge verdict", judge_verdict if judge_verdict else "unset"),
        ]

        if not (logs_dir / "test_reasoning.md").exists():
            (logs_dir / "test_reasoning.md").write_text(
                "# Eval Reasoning\n\nNo reasoning log was produced.\n",
                encoding="utf-8",
            )
        if not (logs_dir / "issues.md").exists():
            (logs_dir / "issues.md").write_text("# Eval Issues\n\nNo issues recorded.\n", encoding="utf-8")

    end_iso = iso_now()
    final_positive_count, final_negative_count, _ = count_spec_test_cases(cases_dir / "cases.json")

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
        impl_java=impl_java,
        prompt_path=prompt_path,
        stdout_path=stdout_path,
        stderr_path=stderr_path,
        last_message_path=last_message_path,
        usage=usage,
        positive_count=final_positive_count,
        negative_count=final_negative_count,
        extras=extras,
        judgment=judgment,
    )
    print(str(workspace))
    return 0 if status == "Success" else 1


if __name__ == "__main__":
    raise SystemExit(main())

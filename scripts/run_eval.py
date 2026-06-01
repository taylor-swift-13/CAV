#!/usr/bin/env python3
"""Eval-stage runner: the critic that checks whether a contract correctly
characterizes an implementation, using concrete positive/negative cases.

Mirrors ``run_contract.py``: bootstrap a workspace, build a prompt around
``skills/eval/SKILL.md``, run the agent (codex/claude), and gate on
``logs/metrics.md`` ending in ``Final Result: Success``.

Extra: *computable* ``needs_judge`` clauses are discharged deterministically.
The agent emits ``evaluation/compute_queries.json`` (closed Coq terms); this
runner evaluates them with ``vm_compute`` via ``coq_runner`` into
``evaluation/compute_results.json`` and runs a second agent pass to fold the
results into the final verdict.
"""
from __future__ import annotations

import argparse
import datetime as dt
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

REPO_ROOT = Path(__file__).resolve().parents[1]
import coq_runner

DEFAULT_SKILL = REPO_ROOT / "skills" / "eval" / "SKILL.md"
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


def emit_log(message: str) -> None:
    print(f"[eval] {message}", flush=True)


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
            [codex_bin, "exec", "--help"], stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True, cwd=REPO_ROOT, env=env, timeout=10,
        )
    except (subprocess.SubprocessError, OSError):
        return False
    return "--reasoning-effort" in proc.stdout


def filter_stderr_in_place(stderr_log: Path) -> None:
    if not stderr_log.exists():
        return
    kept = [
        ln for ln in stderr_log.read_text(encoding="utf-8", errors="replace").splitlines()
        if not any(p in ln for p in NOISE_PATTERNS)
    ]
    stderr_log.write_text("\n".join(kept) + ("\n" if kept else ""), encoding="utf-8")


def metrics_path(workspace_path: Path) -> Path:
    return workspace_path / "logs" / "metrics.md"


def final_result_path(workspace_path: Path) -> Path:
    return workspace_path / "logs" / "final_result.md"


def bootstrap_workspace(workspace_path: Path, input_c: Path, input_v: Path | None) -> None:
    for sub in ("logs", "original", "cases", "evaluation"):
        (workspace_path / sub).mkdir(parents=True, exist_ok=True)
    shutil.copy2(input_c, workspace_path / "original" / input_c.name)
    if input_v is not None and input_v.exists():
        shutil.copy2(input_v, workspace_path / "original" / input_v.name)


def build_prompt(
    *, skill_path: Path, input_c: Path, input_v: Path | None, function_name: str,
    workspace_path: Path, num_positive: int, num_negative: int,
    compute_results: Path | None,
) -> str:
    v_line = f"- Companion V: `{input_v}`\n" if input_v and input_v.exists() else ""
    lines = [
        f"Follow this skill as the complete workflow: {skill_path}",
        "",
        "Inputs:",
        f"- Implementation/spec C: `{input_c}`",
    ]
    if v_line:
        lines.append(v_line.rstrip())
    lines += [
        f"- Target function: `{function_name}`",
        f"- Workspace: `{workspace_path}`",
        f"- Cases directory: `{workspace_path / 'cases'}`",
        f"- Evaluation directory: `{workspace_path / 'evaluation'}`",
        f"- Required positive cases: `{num_positive}`",
        f"- Required negative cases: `{num_negative}`",
        "",
        "Stage boundary:",
        "- Eval only judges semantic adequacy by spec-test and the final LLM judge.",
        "- Contract runner owns check_spec_wellformed, coqc parse/compile gate for input/<name>.v, verify-annotation scan, and forbidden-assumption scan.",
        "- Eval owns spec-test, final semantic judge, and compute_queries/vm_compute for concrete closed terms.",
    ]
    if compute_results is not None:
        lines += [
            "",
            f"Compute results: `{compute_results}` (FINALIZE pass — also follow MODE_FINALIZE.md per SKILL.md §8).",
        ]
    return "\n".join(lines) + "\n"


def run_agent_once(
    *, agent: str, codex_bin: str, claude_bin: str, model: str,
    reasoning_effort: str, prompt: str, logs_dir: Path, run_label: str,
    env: dict[str, str], timeout_seconds: int,
) -> tuple[int, dict[str, int] | None, Path]:
    """One agent session. Returns (returncode, usage, stdout_path)."""
    prompt_path = logs_dir / f"agent_prompt_{run_label}.txt"
    stdout_jsonl = logs_dir / f"agent_stdout_{run_label}.jsonl"
    stderr_log = logs_dir / f"agent_stderr_{run_label}.log"
    last_message_path = logs_dir / f"agent_last_message_{run_label}.txt"
    prompt_path.write_text(prompt, encoding="utf-8")

    if agent == "claude":
        cmd = [claude_bin, "--print", "--dangerously-skip-permissions", "--add-dir",
               str(REPO_ROOT), "--output-format", "stream-json", "--verbose"]
        if model:
            cmd.extend(["--model", model])
        if reasoning_effort and agent_config.claude_supports_flag(claude_bin, REPO_ROOT, env, "--effort"):
            cmd.extend(["--effort", reasoning_effort])
    else:
        cmd = [codex_bin, "--dangerously-bypass-approvals-and-sandbox", "exec",
               "--json", "--skip-git-repo-check", "-C", str(REPO_ROOT),
               "-o", str(last_message_path)]
        if model:
            cmd.extend(["--model", model])
        if reasoning_effort and codex_supports_reasoning_effort(codex_bin, env):
            cmd.extend(["--reasoning-effort", reasoning_effort])
        cmd.append("-")

    try:
        with stdout_jsonl.open("w", encoding="utf-8") as out_f, stderr_log.open("w", encoding="utf-8") as err_f:
            proc = subprocess.run(cmd, input=prompt, text=True, stdout=out_f,
                                  stderr=err_f, cwd=REPO_ROOT, env=env, timeout=timeout_seconds)
        rc = proc.returncode
    except subprocess.TimeoutExpired:
        rc = 124
    filter_stderr_in_place(stderr_log)
    if agent == "claude":
        last_message = agent_metrics.extract_claude_last_message(stdout_jsonl)
        if last_message is not None:
            last_message_path.write_text(last_message, encoding="utf-8")
        elif stdout_jsonl.exists():
            last_message_path.write_text(stdout_jsonl.read_text(encoding="utf-8", errors="replace"), encoding="utf-8")
    usage = agent_metrics.parse_usage(agent, stdout_jsonl)
    return rc, usage, stdout_jsonl


def evaluate_compute_queries(workspace_path: Path, env: dict[str, str]) -> int:
    """Evaluate evaluation/compute_queries.json via coqc; write compute_results.json.

    Returns the number of queries evaluated (0 if no query file / empty).
    """
    queries_path = workspace_path / "evaluation" / "compute_queries.json"
    if not queries_path.exists():
        return 0
    try:
        data = json.loads(queries_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return 0
    queries = data.get("queries") if isinstance(data, dict) else data
    if not isinstance(queries, list) or not queries:
        return 0

    compute_dir = workspace_path / "evaluation" / "compute"
    compute_dir.mkdir(parents=True, exist_ok=True)
    logs_dir = workspace_path / "logs"
    original_dir = workspace_path / "original"
    extra_q = [(str(original_dir), "")] if any(original_dir.glob("*.v")) else None

    results = []
    stdout_log, stderr_log = [], []
    for q in queries:
        qid = str(q.get("id", f"q{len(results)}"))
        coq_expr = q.get("coq_expr", "")
        requires = q.get("requires", []) or []
        # coqc derives the module name from the filename: keep it a valid Coq
        # identifier (no dots/spaces), since query ids look like "pos03.c1".
        safe = re.sub(r"[^0-9A-Za-z_]", "_", qid)
        if not safe or not (safe[0].isalpha() or safe[0] == "_"):
            safe = "q_" + safe
        v_path = compute_dir / f"{safe}.v"
        body = "\n".join(requires) + f"\nDefinition __r := {coq_expr}.\nEval vm_compute in __r.\n"
        v_path.write_text(body, encoding="utf-8")
        rc, out, err = coq_runner.run_coqc(v_path, extra_q=extra_q, env=env, timeout_seconds=120)
        normal_form = coq_runner.parse_eval_normal_form(out) if rc == 0 else None
        results.append({
            "id": qid, "clause": q.get("clause", ""), "coq_expr": coq_expr,
            "rc": rc, "normal_form": normal_form, "ok": rc == 0 and normal_form is not None,
        })
        stdout_log.append(f"### {qid}\n$ coqc {v_path.name}\n{out}")
        stderr_log.append(f"### {qid}\n{err}")

    (workspace_path / "evaluation" / "compute_results.json").write_text(
        json.dumps({"results": results}, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    (logs_dir / "compute_stdout.log").write_text("\n".join(stdout_log) + "\n", encoding="utf-8")
    (logs_dir / "compute_stderr.log").write_text("\n".join(stderr_log) + "\n", encoding="utf-8")
    # Drop the .vo/.glob/.aux coqc left next to the compute .v files.
    coq_runner.clean_compile_artifacts(compute_dir)
    return len(results)


def read_final_result_value(workspace_path: Path, marker: str) -> str | None:
    fr = final_result_path(workspace_path)
    if not fr.exists():
        return None
    for line in fr.read_text(encoding="utf-8", errors="replace").splitlines():
        # Accept both `Marker: X` and markdown/list forms like `## Marker: X`.
        if marker in line:
            return line.split(marker, 1)[1].strip()
    return None


def read_spec_verdict(workspace_path: Path) -> str | None:
    return read_final_result_value(workspace_path, "Spec verdict:")


def read_judge_verdict(workspace_path: Path) -> str | None:
    return read_final_result_value(workspace_path, "Judge verdict:")


def artifact_gate(workspace_path: Path, num_positive: int, num_negative: int) -> tuple[bool, str]:
    cases_path = workspace_path / "cases" / "cases.json"
    eval_path = workspace_path / "evaluation" / "evaluation.json"
    if not cases_path.exists():
        return False, f"missing_cases:{cases_path}"
    if not eval_path.exists():
        return False, f"missing_evaluation:{eval_path}"

    try:
        cases_doc = json.loads(cases_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        return False, f"invalid_cases_json:{exc}"
    try:
        eval_doc = json.loads(eval_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        return False, f"invalid_evaluation_json:{exc}"

    positives = cases_doc.get("positive") if isinstance(cases_doc, dict) else None
    negatives = cases_doc.get("negative") if isinstance(cases_doc, dict) else None
    if not isinstance(positives, list) or len(positives) < num_positive:
        return False, f"insufficient_positive_cases:{len(positives) if isinstance(positives, list) else 'missing'}<{num_positive}"
    if not isinstance(negatives, list) or len(negatives) < num_negative:
        return False, f"insufficient_negative_cases:{len(negatives) if isinstance(negatives, list) else 'missing'}<{num_negative}"

    positive_ids = {str(c.get("id")) for c in positives if isinstance(c, dict) and c.get("id") is not None}
    negative_ids = {str(c.get("id")) for c in negatives if isinstance(c, dict) and c.get("id") is not None}
    expected_ids = positive_ids | negative_ids
    eval_cases = eval_doc.get("cases") if isinstance(eval_doc, dict) else None
    if not isinstance(eval_cases, list):
        return False, "evaluation_cases_missing"
    evaluated_ids = {str(c.get("id")) for c in eval_cases if isinstance(c, dict) and c.get("id") is not None}
    missing = sorted(expected_ids - evaluated_ids)
    if missing:
        return False, "evaluation_missing_cases:" + ",".join(missing)

    def has_unresolved_needs_judge(value) -> bool:
        if isinstance(value, dict):
            if value.get("verdict") == "needs_judge":
                return True
            return any(has_unresolved_needs_judge(v) for v in value.values())
        if isinstance(value, list):
            return any(has_unresolved_needs_judge(v) for v in value)
        return False

    if has_unresolved_needs_judge(eval_doc):
        return False, "evaluation_has_unresolved_needs_judge"

    verdict_by_id = {
        str(c.get("id")): c.get("verdict")
        for c in eval_cases
        if isinstance(c, dict) and c.get("id") is not None
    }
    positive_failures = sorted(cid for cid in positive_ids if verdict_by_id.get(cid) != "pass")
    negative_failures = sorted(cid for cid in negative_ids if verdict_by_id.get(cid) != "fail")
    if positive_failures:
        return False, "positive_cases_not_pass:" + ",".join(positive_failures)
    if negative_failures:
        return False, "negative_cases_not_rejected:" + ",".join(negative_failures)
    return True, "artifacts_ok"


def gate_success(workspace_path: Path, num_positive: int, num_negative: int) -> tuple[bool, str]:
    mp = metrics_path(workspace_path)
    if not mp.exists():
        return False, "missing_metrics"
    saw_success = any(ln.strip() == "Final Result: Success"
                      for ln in mp.read_text(encoding="utf-8", errors="replace").splitlines())
    verdict = read_spec_verdict(workspace_path)
    judge = read_judge_verdict(workspace_path)
    artifacts_ok, artifacts_detail = artifact_gate(workspace_path, num_positive, num_negative)
    if saw_success and verdict == "Correct" and judge == "Pass" and artifacts_ok:
        return True, f"spec:{verdict}|judge:{judge}|{artifacts_detail}"
    return False, (
        f"spec:{verdict}|judge:{judge}|agent_final_result_success:{saw_success}|"
        f"artifacts:{artifacts_detail}"
    )


def write_metrics(path: Path, *, status: str, exit_code: int, start_iso: str,
                  end_iso: str, wall_seconds: float, model: str, reasoning_effort: str,
                  agent_rounds: int, compute_evaluated: int, verdict: str | None,
                  judge_verdict: str | None,
                  usage: dict[str, int] | None) -> None:
    lines = [
        "# Eval Metrics", "",
        "- Stage: `eval`",
        f"- Status: `{status}`",
        f"- Exit code: `{exit_code}`",
        f"- Start time: `{start_iso}`",
        f"- End time: `{end_iso}`",
        f"- Wall-clock time (seconds): `{wall_seconds:.2f}`",
        f"- Model: `{model}`",
        f"- Reasoning effort: `{reasoning_effort}`",
        f"- Agent rounds: `{agent_rounds}`",
        f"- Compute queries evaluated: `{compute_evaluated}`",
        f"- Spec verdict: `{verdict}`",
        f"- Judge verdict: `{judge_verdict}`",
    ]
    lines.extend(agent_metrics.usage_lines(usage))
    lines.append(f"Final Result: {status}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Run the eval critic over a C/QCP contract.")
    p.add_argument("input_c", help="Path to the contract C file (default input/<name>.c).")
    p.add_argument("--function-name", help="Target function; defaults to file stem.")
    p.add_argument("--num-positive", type=int, default=None)
    p.add_argument("--num-negative", type=int, default=None)
    p.add_argument("--skill", default=str(DEFAULT_SKILL))
    p.add_argument("--workspace-name")
    p.add_argument("--timestamp")
    p.add_argument("--config", default=None)
    p.add_argument("--agent", choices=["codex", "claude"], default=None)
    p.add_argument("--model", default=None)
    p.add_argument("--reasoning-effort", default=None)
    p.add_argument("--max-agent-rounds", type=int, default=2,
                   help="Cap on agent sessions (round 1 + compute finalize).")
    p.add_argument("--timeout-seconds", type=int, default=900)
    p.add_argument("--dry-run", action="store_true")
    return p


def main() -> int:
    args = build_parser().parse_args()
    input_c = Path(args.input_c)
    if not input_c.is_absolute():
        input_c = (REPO_ROOT / input_c).resolve()
    if not input_c.exists():
        print(f"input C not found: {input_c}", file=sys.stderr)
        return 2
    skill_path = Path(args.skill)
    if not skill_path.is_absolute():
        skill_path = (REPO_ROOT / skill_path).resolve()

    cfg = agent_config.load(args.config)
    agent = args.agent or cfg.agent("codex")
    model = args.model or cfg.default_model(agent, DEFAULT_CLAUDE_MODEL if agent == "claude" else DEFAULT_MODEL)
    reasoning_effort = args.reasoning_effort or cfg.reasoning_effort(DEFAULT_REASONING_EFFORT)
    codex_bin = cfg.bin("codex", "codex")
    claude_bin = cfg.bin("claude", "claude")
    num_positive = args.num_positive if args.num_positive is not None else cfg.eval_num("num_positive", 4)
    num_negative = args.num_negative if args.num_negative is not None else cfg.eval_num("num_negative", 4)

    function_name = args.function_name or input_c.stem
    input_v = input_c.with_suffix(".v")
    input_v = input_v if input_v.exists() else None

    stem = args.workspace_name or input_c.stem
    ts = args.timestamp or timestamp_now()
    workspace_path = OUTPUT_ROOT / f"eval_{ts}_{stem}"
    bootstrap_workspace(workspace_path, input_c, input_v)
    logs_dir = workspace_path / "logs"
    env = build_agent_env(logs_dir)
    emit_log(f"workspace={workspace_path}")
    emit_log(f"function_name={function_name} agent={agent} model={model} cases={num_positive}+{num_negative}")

    if args.dry_run:
        write_metrics(metrics_path(workspace_path), status="Success", exit_code=0,
                      start_iso=iso_now(), end_iso=iso_now(), wall_seconds=0.0, model=model,
                      reasoning_effort=reasoning_effort, agent_rounds=0, compute_evaluated=0,
                      verdict=None, judge_verdict=None, usage=None)
        emit_log("dry_run=true")
        print(str(workspace_path))
        return 0

    start_wall = time.time()
    start_iso = iso_now()
    usage_total: dict[str, int] | None = None
    last_rc = 0
    compute_evaluated = 0
    rounds = 0
    deadline = start_wall + args.timeout_seconds

    while rounds < max(1, args.max_agent_rounds):
        rounds += 1
        remaining = int(max(1, deadline - time.time()))
        compute_results = (workspace_path / "evaluation" / "compute_results.json") if rounds > 1 else None
        prompt = build_prompt(
            skill_path=skill_path, input_c=input_c, input_v=input_v,
            function_name=function_name, workspace_path=workspace_path,
            num_positive=num_positive, num_negative=num_negative,
            compute_results=compute_results if (compute_results and compute_results.exists()) else None,
        )
        run_label = dt.datetime.now().strftime("%Y%m%d_%H%M%S") + f"_r{rounds}"
        emit_log(f"agent_round={rounds} remaining={remaining}")
        last_rc, usage, _ = run_agent_once(
            agent=agent, codex_bin=codex_bin, claude_bin=claude_bin, model=model,
            reasoning_effort=reasoning_effort, prompt=prompt, logs_dir=logs_dir,
            run_label=run_label, env=env, timeout_seconds=remaining)
        usage_total = agent_metrics.add_usage(usage_total, usage)

        # Discharge any computable needs_judge clauses, then loop to finalize.
        n = evaluate_compute_queries(workspace_path, env)
        if n:
            compute_evaluated += n
            emit_log(f"compute_queries_evaluated={n}")
        ok, detail = gate_success(workspace_path, num_positive, num_negative)
        if ok:
            emit_log(f"gate_pass {detail}")
            break
        if not n:
            emit_log(f"gate_not_met_no_more_compute {detail}")
            break  # nothing new to fold; further rounds won't help
        if time.time() >= deadline:
            break

    ok, _ = gate_success(workspace_path, num_positive, num_negative)
    status = "Success" if ok else "Fail"
    verdict = read_spec_verdict(workspace_path)
    judge_verdict = read_judge_verdict(workspace_path)
    write_metrics(metrics_path(workspace_path), status=status, exit_code=last_rc,
                  start_iso=start_iso, end_iso=iso_now(), wall_seconds=time.time() - start_wall,
                  model=model, reasoning_effort=reasoning_effort, agent_rounds=rounds,
                  compute_evaluated=compute_evaluated, verdict=verdict,
                  judge_verdict=judge_verdict, usage=usage_total)
    emit_log(
        f"status={status} verdict={verdict} judge={judge_verdict} "
        f"rounds={rounds} compute_evaluated={compute_evaluated}"
    )
    print(str(workspace_path))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

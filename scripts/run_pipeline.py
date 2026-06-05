#!/usr/bin/env python3
"""Closed-loop multi-agent orchestrator for the C/QCP flow.

One critic-gated contract block plus a deterministic verify audit check:

  * Contract block: ``run_contract`` -> ``run_eval``. If the eval critic does not
    return ``Spec verdict: Correct`` and rounds remain, re-run the contract with
    the eval findings injected (``--restart-context-file``).
  * Verify block: ``run_verify``. The verify runner's deterministic audit check
    is the post-verify gate.
  * Cost: roll every workspace up with ``agent_metrics.write_pipeline_cost_summary``.

Each block is a hand-rolled budget loop rather than ``agent_loop.run`` because the
orchestrator must carry each critic's findings forward into the *next* solver run
(``agent_loop.run`` only feeds restart context to its first attempt).
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import agent_metrics
import agent_config

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = REPO_ROOT / "scripts"
OUTPUT_ROOT = REPO_ROOT / "output"
INPUT_ROOT = REPO_ROOT / "input"


def emit(msg: str) -> None:
    print(f"[pipeline] {msg}", flush=True)


def run_stage(cmd: list[str]) -> int:
    """Run a sub-runner, streaming its output. Return its exit code."""
    emit("$ " + " ".join(str(c) for c in cmd))
    proc = subprocess.run(cmd, cwd=REPO_ROOT)
    return proc.returncode


def read_line_value(path: Path, marker: str) -> str | None:
    if not path.exists():
        return None
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        if marker in line:
            return line.split(marker, 1)[1].strip()
    return None


def read_eval_gate(eval_ws: Path) -> tuple[str | None, str | None, bool]:
    final_result = eval_ws / "logs" / "final_result.md"
    metrics = eval_ws / "logs" / "metrics.md"
    spec_verdict = read_line_value(final_result, "Spec verdict:")
    judge_verdict = read_line_value(final_result, "Judge verdict:")
    runner_success = False
    if metrics.exists():
        runner_success = any(
            line.strip() == "Final Result: Success"
            for line in metrics.read_text(encoding="utf-8", errors="replace").splitlines()
        )
    return spec_verdict, judge_verdict, runner_success


def write_findings(dest: Path, *, title: str, sources: list[Path]) -> Path:
    """Concatenate critic outputs into one restart-context file for the solver."""
    parts = [f"# {title}\n"]
    for src in sources:
        if src.exists():
            parts.append(f"\n## {src.relative_to(OUTPUT_ROOT) if OUTPUT_ROOT in src.parents else src.name}\n")
            parts.append(src.read_text(encoding="utf-8", errors="replace"))
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text("\n".join(parts) + "\n", encoding="utf-8")
    return dest


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Full contract -> eval -> verify orchestrator.")
    p.add_argument("target", help="raw/<name>.md (full flow) or input/<name>.c (skip contract).")
    p.add_argument("--function-name")
    p.add_argument(
        "--dataset",
        default=None,
        help="Dataset label for raw/<dataset>/ input. Full raw runs write generated C/V under input/<dataset>_<timestamp>/ to avoid conflicts.",
    )
    p.add_argument("--contract-rounds", type=int, default=None, help=argparse.SUPPRESS)
    # Timeout defaults are None here so config/agents.json `timeouts` can supply
    # them; an explicit flag still wins. Resolved in main() (CLI > config > builtin).
    p.add_argument("--contract-timeout", type=int, default=None)
    p.add_argument("--eval-timeout", type=int, default=None)
    p.add_argument("--verify-timeout", type=int, default=None)
    p.add_argument("--skip-eval", action="store_true", help="Skip the eval gate before verify.")
    p.add_argument("--force", action="store_true", help="Continue to verify even if eval never reaches Correct.")
    p.add_argument("--config", default=None)
    p.add_argument("--agent", choices=["codex", "claude", "kimicode"], default=None)
    p.add_argument("--model", default=None)
    p.add_argument("--reasoning-effort", default=None)
    p.add_argument("--dry-run", action="store_true")
    return p


def common_flags(args) -> list[str]:
    flags: list[str] = []
    if args.config:
        flags += ["--config", args.config]
    if args.agent:
        flags += ["--agent", args.agent]
    if args.model:
        flags += ["--model", args.model]
    if args.reasoning_effort:
        flags += ["--reasoning-effort", args.reasoning_effort]
    if args.dry_run:
        flags += ["--dry-run"]
    return flags


def main() -> int:
    args = build_parser().parse_args()
    # Resolve per-stage timeouts: explicit CLI flag > config/agents.json > builtin.
    cfg = agent_config.load(args.config)
    for stage, builtin in (("contract", 300), ("eval", 900), ("verify", 3600)):
        attr = f"{stage}_timeout"
        if getattr(args, attr) is None:
            setattr(args, attr, cfg.timeout(stage, builtin))
    target = Path(args.target)
    if not target.is_absolute():
        target = (REPO_ROOT / target).resolve()
    if not target.exists():
        print(f"target not found: {target}", file=sys.stderr)
        return 2
    name = args.function_name or target.stem
    ds = args.dataset
    label = name  # dataset tag is carried in <name> itself; --dataset only selects raw/input/<ds>/ folders
    is_raw = target.suffix == ".md"
    base_ts = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
    input_dataset = f"{ds}_{base_ts}" if is_raw and ds else (base_ts if is_raw else ds)
    pipeline_dir = OUTPUT_ROOT / f"pipeline_{base_ts}_{label}"
    pipeline_dir.mkdir(parents=True, exist_ok=True)
    workspaces: list[Path] = []
    cf = common_flags(args)
    input_c = (INPUT_ROOT / input_dataset / f"{name}.c") if input_dataset else (INPUT_ROOT / f"{name}.c")

    emit(f"target={target} name={name} raw={is_raw} dir={pipeline_dir}")
    if is_raw:
        emit(f"generated_input_dataset={input_dataset} input_c={input_c}")

    # ---- Contract block (contract -> eval) ----
    eval_verdict = None
    judge_verdict = None
    eval_runner_success = False
    if is_raw:
        restart_file = None
        rnd = 0
        while True:
            rnd += 1
            ts = f"{base_ts}c{rnd}"
            contract_ws = OUTPUT_ROOT / f"contract_{ts}_{label}"
            cmd = [sys.executable, str(SCRIPTS / "run_contract.py"), str(target),
                   "--function-name", name, "--timestamp", ts, "--workspace-name", label,
                   "--timeout-seconds", str(args.contract_timeout), "--dataset", input_dataset, *cf]
            if restart_file:
                cmd += ["--restart-context-file", str(restart_file)]
            contract_rc = run_stage(cmd)
            workspaces.append(contract_ws)
            if contract_rc != 0:
                emit(f"contract round {rnd} returned nonzero; retrying contract with syntax feedback")
                if args.dry_run:
                    break
                if args.contract_rounds is None or rnd < args.contract_rounds:
                    restart_file = write_findings(
                        pipeline_dir / f"contract_findings_r{rnd}.md",
                        title=f"Contract syntax check findings (round {rnd})",
                        sources=[
                            contract_ws / "logs" / "issues.md",
                            contract_ws / "logs" / "metrics.md",
                            contract_ws / "logs" / "continue.md",
                            contract_ws / "input" / f"{name}.c",
                            contract_ws / "input" / f"{name}.v",
                        ],
                    )
                    continue
                _finish(workspaces, pipeline_dir, args, name, status="contract_syntax_check_failed", generated_input=input_c if is_raw else None)
                return 1

            if args.skip_eval:
                eval_verdict = "Correct"  # gate bypassed
                break

            ets = f"{base_ts}e{rnd}"
            eval_ws = OUTPUT_ROOT / f"eval_{ets}_{label}"
            ecmd = [sys.executable, str(SCRIPTS / "run_eval.py"), str(input_c),
                    "--function-name", name, "--timestamp", ets, "--workspace-name", label,
                    "--timeout-seconds", str(args.eval_timeout), *cf]
            eval_rc = run_stage(ecmd)
            workspaces.append(eval_ws)
            eval_verdict, judge_verdict, eval_runner_success = read_eval_gate(eval_ws)
            emit(
                f"contract round {rnd}: eval rc={eval_rc} "
                f"spec={eval_verdict} judge={judge_verdict} runner_success={eval_runner_success}"
            )
            if args.dry_run:
                break  # wiring exercised; no real verdict to gate on
            if eval_rc == 0 and eval_verdict == "Correct" and judge_verdict == "Pass" and eval_runner_success:
                break
            if args.contract_rounds is None or rnd < args.contract_rounds:
                restart_file = write_findings(
                    pipeline_dir / f"eval_findings_r{rnd}.md", title=f"Eval findings (round {rnd})",
                    sources=[
                        eval_ws / "logs" / "final_result.md",
                        eval_ws / "logs" / "metrics.md",
                        eval_ws / "evaluation" / "evaluation.json",
                    ])
                continue
            break

        if not args.skip_eval and not args.dry_run and (
            eval_verdict != "Correct" or judge_verdict != "Pass" or not eval_runner_success
        ) and not args.force:
            emit(
                "contract gate not met "
                f"(spec={eval_verdict}, judge={judge_verdict}, runner_success={eval_runner_success}); "
                "stopping before verify (use --force to continue)"
            )
            _finish(workspaces, pipeline_dir, args, name, status="eval_gate_not_met", generated_input=input_c if is_raw else None)
            return 1
    else:
        input_c = target

    # ---- Verify block (run_verify owns retry and deterministic audit check) ----
    ts = f"{base_ts}v"
    verify_ws = OUTPUT_ROOT / f"verify_{ts}_{label}"
    cmd = [sys.executable, str(SCRIPTS / "run_verify.py"), str(input_c),
           "--function-name", name, "--timestamp", ts, "--workspace-name", label,
           "--timeout-seconds", str(args.verify_timeout), *cf]
    verify_rc = run_stage(cmd)
    workspaces.append(verify_ws)
    verify_ok = verify_rc == 0 or args.dry_run
    emit(f"verify audit_check={'passed' if verify_ok else f'failed exit={verify_rc}'}")

    status = "success" if verify_ok else "audit_check_failed"
    _finish(workspaces, pipeline_dir, args, name, status=status, generated_input=input_c if is_raw else None)
    return 0 if status == "success" else 1


def _finish(workspaces, pipeline_dir, args, name, *, status, generated_input: Path | None = None) -> None:
    # ---- Cost summary ----
    cost = pipeline_dir / "cost_summary.md"
    try:
        agent_metrics.write_pipeline_cost_summary(workspaces, cost)
        emit(f"cost_summary={cost}")
    except Exception as exc:  # noqa: BLE001 - cost rollup is best-effort
        emit(f"cost_summary_failed: {exc}")

    summary = {"status": status, "name": name,
               "workspaces": [str(w) for w in workspaces]}
    if generated_input is not None:
        summary["generated_input"] = str(generated_input)
        summary["generated_input_dir"] = str(generated_input.parent)
    (pipeline_dir / "pipeline_summary.json").write_text(
        json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    emit(f"status={status} workspaces={len(workspaces)} summary={pipeline_dir / 'pipeline_summary.json'}")


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Top-level orchestrator for the Java/OpenJML pipeline.

Two serial solver+critic blocks, then one experience consolidation:

  1. contract block: always runs the contract solver. If ``--eval`` is enabled,
     the eval critic also runs and may overturn the result in a bounded restart
     loop.
  2. verify block: always runs the verify solver. If ``--audit`` is enabled,
     the audit critic also runs and may overturn the result in a bounded restart
     loop.
  3. consolidation: one dedicated unit, scoped to whatever ran
     (contract-only / verify-only / end-to-end), merges this run's lessons into
     ``experiences/general``.

Each block is independently invocable via ``--only contract|verify|all``. The
whole pipeline is bounded by ``--total-budget-seconds`` and
``--max-overturn-rounds``. Timeout is failure; the solver loop never restarts on
timeout (see :mod:`agent_loop`).
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import datetime as dt
from pathlib import Path
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import agent_config
import agent_metrics
import experience_consolidate
from run_eval import read_spec_verdict
from run_audit import read_audit_verdict


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = REPO_ROOT / "scripts"
OUTPUT_ROOT = REPO_ROOT / "output"
INPUT_ROOT = REPO_ROOT / "input"
DEFAULT_MODEL = "gpt-5.4"
DEFAULT_CLAUDE_MODEL = "sonnet"
DEFAULT_REASONING_EFFORT = "medium"


def emit(msg: str) -> None:
    print(f"[pipeline] {msg}", flush=True)


def timestamp_now() -> str:
    return dt.datetime.now().strftime("%Y%m%d_%H%M%S")


def class_name_from_stem(stem: str) -> str:
    return "".join(p[:1].upper() + p[1:] for p in stem.replace("-", "_").split("_") if p)


@dataclass
class BlockResult:
    status: str                       # "Success" | "Fail"
    detail: str = ""
    workspaces: list[Path] = field(default_factory=list)


# A critic returns one of three outcomes. "inconclusive" must NOT be treated as
# pass: a critic that could not render a verdict (crashed, timed out, or judged
# the case undecidable) means that part of the result is unvalidated.
CRITIC_OK = "ok"
CRITIC_OVERTURN = "overturn"
CRITIC_INCONCLUSIVE = "inconclusive"


def classify_eval(eval_ws: Path | None) -> tuple[str, str | None]:
    """Map a spec-test eval workspace to (outcome, verdict)."""
    if eval_ws is None:
        return CRITIC_INCONCLUSIVE, None
    verdict = read_spec_verdict(eval_ws / "logs" / "final_result.md")
    if verdict == "Buggy":
        return CRITIC_OVERTURN, verdict
    if verdict == "Correct":
        return CRITIC_OK, verdict
    # "Inconclusive", or no decisive verdict (crash / missing file).
    return CRITIC_INCONCLUSIVE, verdict


def classify_audit(audit_ws: Path | None) -> tuple[str, str | None]:
    if audit_ws is None:
        return CRITIC_INCONCLUSIVE, None
    verdict = read_audit_verdict(audit_ws / "logs" / "final_result.md")
    if verdict == "NotVerified":
        return CRITIC_OVERTURN, verdict
    if verdict in ("VerifiedClean", "VerifiedWithWarnings"):
        return CRITIC_OK, verdict
    return CRITIC_INCONCLUSIVE, verdict


def run_stage(script: str, stage_args: list[str]) -> tuple[int, Path | None]:
    """Run a runner subprocess, stream its output, return (exit_code, workspace).

    The runners print progress as ``[stage] ...`` lines and the workspace path as
    the final stdout line.
    """
    cmd = [sys.executable, str(SCRIPTS / script), *stage_args]
    emit(f"exec {script} {' '.join(stage_args)}")
    last_line: str | None = None
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            text=True, cwd=REPO_ROOT)
    assert proc.stdout is not None
    for line in proc.stdout:
        sys.stdout.write(line)
        sys.stdout.flush()
        if line.strip():
            last_line = line.strip()
    proc.wait()
    ws = Path(last_line) if last_line and last_line.startswith(str(OUTPUT_ROOT)) else None
    return proc.returncode, ws


def write_findings(pipeline_logs: Path, label: str, *paths: Path) -> Path:
    pipeline_logs.mkdir(parents=True, exist_ok=True)
    out = pipeline_logs / f"{label}_findings.md"
    parts = []
    for p in paths:
        if p.exists():
            parts.append(f"# {p.relative_to(REPO_ROOT) if p.is_relative_to(REPO_ROOT) else p}\n\n"
                         + p.read_text(encoding="utf-8", errors="replace"))
    out.write_text("\n\n".join(parts) or "(no findings file produced)\n", encoding="utf-8")
    return out


def remaining(deadline: float) -> int:
    return int(deadline - time.time())


def run_contract_block(
    *, raw_path: Path, stem: str, function_name: str, deadline: float,
    max_overturn: int, pipeline_logs: Path, common: list[str], dry_run: bool,
    use_eval: bool, eval_cases: int | None = None,
) -> BlockResult:
    """Run contract, optionally with eval as a bounded critic loop."""
    workspaces: list[Path] = []
    contract_ws: Path | None = None
    eval_findings: Path | None = None
    input_java = INPUT_ROOT / f"{stem}.java"

    for overturn in range(max_overturn + 1):
        if remaining(deadline) <= 0:
            return BlockResult("Fail", "budget exhausted before contract round", workspaces)
        c_args = [str(raw_path), "--function-name", function_name, "--workspace-name", stem,
                  "--timeout-seconds", str(remaining(deadline)), *common]
        if contract_ws is not None:
            c_args += ["--resume-workspace", str(contract_ws)]
        if eval_findings is not None:
            c_args += ["--restart-from", str(eval_findings)]
        if dry_run:
            c_args.append("--dry-run")
        rc, contract_ws = run_stage("run_contract.py", c_args)
        if contract_ws:
            workspaces = [w for w in workspaces if w != contract_ws] + [contract_ws]
        if rc != 0:
            return BlockResult("Fail", f"contract solver failed (exit {rc})", workspaces)
        if dry_run:
            return BlockResult("Success", "dry run", workspaces)
        if not use_eval:
            return BlockResult("Success", "contract solver passed (eval disabled)", workspaces)

        # critic: eval evaluates whether the spec characterizes the impl. It
        # returns a decisive `Spec verdict:` (Correct / Buggy / Inconclusive).
        if remaining(deadline) <= 0:
            return BlockResult("Fail", "budget exhausted before eval", workspaces)
        e_args = [str(input_java), "--class-name", class_name_from_stem(stem),
                  "--method-name", function_name,
                  "--timeout-seconds", str(remaining(deadline)), *common]
        if eval_cases:
            e_args += ["--num-positive", str(eval_cases), "--num-negative", str(eval_cases)]
        _, eval_ws = run_stage("run_eval.py", e_args)
        if eval_ws:
            workspaces.append(eval_ws)
        outcome, verdict = classify_eval(eval_ws)
        emit(f"eval outcome={outcome} verdict={verdict}")
        if outcome == CRITIC_OVERTURN:
            eval_findings = write_findings(
                pipeline_logs, f"eval_overturn_{overturn + 1}",
                eval_ws / "logs" / "final_result.md", eval_ws / "logs" / "issues.md",
            )
            emit(f"eval overturned contract; restarting contract (round {overturn + 1})")
            continue
        if outcome == CRITIC_INCONCLUSIVE:
            # Do not certify on an undecided critic, and do not loop on it.
            return BlockResult("Fail", f"eval inconclusive (verdict={verdict}); spec not validated", workspaces)
        return BlockResult("Success", f"eval verdict={verdict}", workspaces)

    return BlockResult("Fail", f"max overturn rounds ({max_overturn}) exhausted at contract", workspaces)


def run_verify_block(
    *, input_java: Path, class_name: str, deadline: float, max_overturn: int,
    pipeline_logs: Path, common: list[str], export_examples: bool, dry_run: bool,
    use_audit: bool,
) -> BlockResult:
    """Run verify, optionally with audit as a bounded critic loop."""
    workspaces: list[Path] = []
    verify_ws: Path | None = None
    audit_findings: Path | None = None
    stem = input_java.stem

    for overturn in range(max_overturn + 1):
        if remaining(deadline) <= 0:
            return BlockResult("Fail", "budget exhausted before verify round", workspaces)
        v_args = [str(input_java), "--class-name", class_name, "--workspace-name", stem,
                  "--timeout-seconds", str(remaining(deadline)), *common]
        if verify_ws is not None:
            v_args += ["--resume-workspace", str(verify_ws)]
        if audit_findings is not None:
            v_args += ["--restart-from", str(audit_findings)]
        if export_examples:
            v_args.append("--export-examples")
        if dry_run:
            v_args.append("--dry-run")
        rc, verify_ws = run_stage("run_verify.py", v_args)
        if verify_ws:
            workspaces = [w for w in workspaces if w != verify_ws] + [verify_ws]
        if rc != 0:
            return BlockResult("Fail", f"verify solver failed (exit {rc})", workspaces)
        if dry_run:
            return BlockResult("Success", "dry run", workspaces)
        if not use_audit:
            return BlockResult("Success", "verify solver passed (audit disabled)", workspaces)

        # critic: audit checks the proof for anti-cheating.
        if remaining(deadline) <= 0:
            return BlockResult("Fail", "budget exhausted before audit", workspaces)
        a_args = ["--workspace", str(verify_ws),
                  "--timeout-seconds", str(remaining(deadline)), *common]
        _, audit_ws = run_stage("run_audit.py", a_args)
        if audit_ws:
            workspaces.append(audit_ws)
        outcome, verdict = classify_audit(audit_ws)
        emit(f"audit outcome={outcome} verdict={verdict}")
        if outcome == CRITIC_OVERTURN:
            audit_findings = write_findings(
                pipeline_logs, f"audit_overturn_{overturn + 1}",
                audit_ws / "audit" / "findings.md", audit_ws / "logs" / "final_result.md",
            )
            emit(f"audit overturned verify; restarting verify (round {overturn + 1})")
            continue
        if outcome == CRITIC_INCONCLUSIVE:
            return BlockResult("Fail", f"audit inconclusive (verdict={verdict}); proof not validated", workspaces)
        return BlockResult("Success", f"audit verdict={verdict}", workspaces)

    return BlockResult("Fail", f"max overturn rounds ({max_overturn}) exhausted at verify", workspaces)


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Java/OpenJML pipeline (contract, optional eval, verify, optional audit, consolidate).")
    p.add_argument("target", help="raw/<name>.md for contract/all; input/<name>.java for verify-only.")
    p.add_argument("--function-name", help="Target method/class for contract (required unless --only verify).")
    p.add_argument("--class-name", help="Java class name for verify. Defaults to PascalCase stem.")
    p.add_argument("--only", choices=["contract", "verify", "all"], default="all")
    p.add_argument("--eval", action="store_true",
                   help="Enable eval as the contract critic. Disabled by default.")
    p.add_argument("--audit", action="store_true",
                   help="Enable audit as the verify critic. Disabled by default.")
    p.add_argument("--total-budget-seconds", type=int, default=7200,
                   help="Total wall-clock budget for the whole pipeline.")
    p.add_argument("--max-overturn-rounds", type=int, default=2,
                   help="Max times a critic may overturn its solver before giving up.")
    p.add_argument("--eval-cases", type=int, default=None,
                   help="Positive=negative case count for the eval critic (default: eval's own default of 4).")
    p.add_argument("--config", default=None,
                   help="Path to agents.json (default: config/agents.json or $CAV_AGENT_CONFIG).")
    p.add_argument("--agent", choices=["codex", "claude"], default=None,
                   help="Override config 'agent'.")
    p.add_argument("--model", default=None, help="Override config solver model.")
    p.add_argument("--reasoning-effort", default=None)
    p.add_argument("--codex-bin", default=None)
    p.add_argument("--claude-bin", default=None)
    p.add_argument("--export-examples", action="store_true")
    p.add_argument("--dry-run", action="store_true")
    return p


def main() -> int:
    args = build_parser().parse_args()
    target = Path(args.target)
    if not target.is_absolute():
        target = (REPO_ROOT / target).resolve()

    if args.eval_cases is not None and not args.eval:
        print("--eval-cases requires --eval", file=sys.stderr)
        return 2

    cfg = agent_config.load(args.config)
    agent = args.agent or cfg.agent("codex")
    model = args.model or cfg.solver_model(agent, DEFAULT_CLAUDE_MODEL if agent == "claude" else DEFAULT_MODEL)
    reasoning = args.reasoning_effort or cfg.reasoning_effort(DEFAULT_REASONING_EFFORT)
    codex_bin = args.codex_bin or cfg.bin("codex", "codex")
    claude_bin = args.claude_bin or cfg.bin("claude", "claude")
    common = ["--agent", agent, "--model", model,
              "--reasoning-effort", reasoning,
              "--codex-bin", codex_bin, "--claude-bin", claude_bin]
    if args.config:
        common += ["--config", args.config]
    rc = {"agent": agent, "codex_bin": codex_bin, "claude_bin": claude_bin,
          "reasoning": reasoning, "consolidate_model": cfg.consolidate_model(model),
          "dry_run": args.dry_run}
    deadline = time.time() + args.total_budget_seconds
    scope = args.only
    ts = timestamp_now()
    all_workspaces: list[Path] = []

    if args.only in ("contract", "all"):
        stem = target.stem
        pipeline_logs = OUTPUT_ROOT / f"pipeline_{ts}_{stem}" / "logs"
        if not args.function_name:
            print("--function-name is required for contract/all", file=sys.stderr)
            return 2
        emit(f"=== contract block (stem={stem}) ===")
        cb = run_contract_block(
            raw_path=target, stem=stem, function_name=args.function_name,
            deadline=deadline, max_overturn=args.max_overturn_rounds,
            pipeline_logs=pipeline_logs, common=common, dry_run=args.dry_run,
            use_eval=args.eval, eval_cases=args.eval_cases,
        )
        all_workspaces += cb.workspaces
        emit(f"contract block: {cb.status} ({cb.detail})")
        if cb.status != "Success":
            _consolidate(scope, all_workspaces, pipeline_logs, rc)
            emit("pipeline FAILED at contract block")
            return 1
        input_java = INPUT_ROOT / f"{stem}.java"
        class_name = args.class_name or class_name_from_stem(stem)
    else:
        input_java = target
        stem = target.stem
        pipeline_logs = OUTPUT_ROOT / f"pipeline_{ts}_{stem}" / "logs"
        class_name = args.class_name or class_name_from_stem(stem)

    if args.only in ("verify", "all"):
        emit(f"=== verify block (class={class_name}) ===")
        vb = run_verify_block(
            input_java=input_java, class_name=class_name, deadline=deadline,
            max_overturn=args.max_overturn_rounds, pipeline_logs=pipeline_logs,
            common=common, export_examples=args.export_examples, dry_run=args.dry_run,
            use_audit=args.audit,
        )
        all_workspaces += vb.workspaces
        emit(f"verify block: {vb.status} ({vb.detail})")
        if vb.status != "Success":
            _consolidate(scope, all_workspaces, pipeline_logs, rc)
            emit("pipeline FAILED at verify block")
            return 1

    _consolidate(scope, all_workspaces, pipeline_logs, rc)
    emit("pipeline SUCCESS")
    return 0


def _consolidate(scope: str, workspaces: list[Path], pipeline_logs: Path, rc: dict) -> None:
    summary = agent_metrics.write_pipeline_cost_summary(workspaces, pipeline_logs / "cost_summary.md")
    emit(f"cost summary -> {summary}")
    emit(f"=== experience consolidation (scope={scope}) ===")
    res = experience_consolidate.consolidate(
        scope=scope, workspaces=workspaces, logs_dir=pipeline_logs,
        agent=rc["agent"], codex_bin=rc["codex_bin"], claude_bin=rc["claude_bin"],
        model=rc["consolidate_model"], reasoning_effort=rc["reasoning"], dry_run=rc["dry_run"],
    )
    emit(f"consolidation: {res.detail}")


if __name__ == "__main__":
    raise SystemExit(main())

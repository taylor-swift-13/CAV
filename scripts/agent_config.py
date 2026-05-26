#!/usr/bin/env python3
"""Shared agent/model configuration so runners need fewer CLI flags.

Resolution precedence for every setting:

    explicit CLI flag  >  config file  >  built-in default

The config file is JSON (Python 3.10 here has no ``tomllib``). Default location
is ``<repo>/config/agents.json``; override with ``--config <path>`` or the
``CAV_AGENT_CONFIG`` environment variable. A missing or malformed file just
falls back to built-in defaults.

Put infrequently-changed things here — model names, agent backend, CLI binary
names, reasoning effort, eval case counts. Keep frequently-changed things
(target file, ``--only``, budgets, ``--dry-run``) as CLI flags.
"""
from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path


# This module lives at <repo>/scripts/, so the repo root is one level up.
REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CONFIG = REPO_ROOT / "config" / "agents.json"


# Backend-neutral efficiency contract injected into every stage's agent prompt
# (claude and codex both read the prompt from stdin). Exploration — reverse-
# engineering tool flags, git archaeology, reading orchestration scripts — was
# the dominant time sink on simple cases, so forbid it up front. Stage-specific
# runners may append their own extra lines.
COMMON_EFFICIENCY_RULES = """
Efficiency rules (exploration is the main time waster on these tasks — do not over-explore):
- Do NOT reverse-engineer tool usage from scratch (no `--help` probes, no `cat`-ing run scripts, no `chmod +x` trial-and-error, no digging through examples to reconstruct flags). Exact commands and templates live in the relevant `experiences/` docs — read those.
- Do NOT read orchestration scripts under `scripts/` (run_*.py, agent_loop.py, coq_runner.py) or your own harness logs (`logs/agent_stdout_*.jsonl`, `logs/agent_prompt_*`). They are irrelevant to the task.
- Do NOT use `git log` / `git show` to hunt for reference solutions.
- Reference reading is limited to `doc/`, `experiences/`, and `QualifiedCProgramming/QCP_examples/` (plus this task's own input / annotated / workspace files). See `doc/PERMISSIONS.md`.
- Stop as soon as the stage's completion criteria are met. The time budget is a hard ceiling, not a target."""


def claude_supports_flag(claude_bin: str, cwd: Path, env: dict[str, str], flag: str) -> bool:
    """Whether `claude --help` advertises ``flag`` (e.g. ``--effort``)."""
    try:
        proc = subprocess.run(
            [claude_bin, "--help"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            cwd=cwd,
            env=env,
            timeout=10,
        )
    except (subprocess.SubprocessError, OSError):
        return False
    return flag in proc.stdout


class Config:
    def __init__(self, data: dict | None):
        self.data = data or {}

    def _section(self, name: str) -> dict:
        section = self.data.get(name)
        return section if isinstance(section, dict) else {}

    def agent(self, builtin: str) -> str:
        return self.data.get("agent") or builtin

    def reasoning_effort(self, builtin: str) -> str:
        return self.data.get("reasoning_effort") or builtin

    def solver_model(self, agent: str, builtin: str) -> str:
        """Model for the contract/verify solver, per agent backend."""
        return self._section("models").get(agent) or builtin

    def consolidate_model(self, builtin: str) -> str:
        return self._section("models").get("consolidate") or builtin

    def bin(self, agent: str, builtin: str) -> str:
        return self._section("bins").get(agent) or builtin

    def eval_num(self, key: str, builtin: int) -> int:
        v = self._section("eval").get(key)
        return v if isinstance(v, int) else builtin

    def default_model(self, agent: str, builtin: str) -> str:
        """Default model for non-solver single-stage runs, per agent backend."""
        return self._section("models").get(agent) or builtin


def load(cli_path: str | None = None) -> Config:
    path: Path | None = None
    if cli_path:
        path = Path(cli_path)
    elif os.environ.get("CAV_AGENT_CONFIG"):
        path = Path(os.environ["CAV_AGENT_CONFIG"])
    elif DEFAULT_CONFIG.exists():
        path = DEFAULT_CONFIG
    if path and path.exists():
        try:
            return Config(json.loads(path.read_text(encoding="utf-8")))
        except (json.JSONDecodeError, OSError):
            return Config({})
    return Config({})

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


# Cross-stage agent-facing rules now live in skills/COMMON.md (referenced by
# each stage's SKILL.md). Stage prompts pass paths + triggers and follow the
# skill; they no longer inline efficiency rules here.


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


def kimicode_reasoning_effort(cli_value: str | None, config_thinking: bool) -> str:
    """Normalize Kimi's boolean thinking switch into the metrics field.

    Kimi Code exposes ``--thinking`` / ``--no-thinking`` rather than
    low/medium/high effort. For CLI compatibility, any explicit false-like
    value disables thinking; other explicit values enable it.
    """
    if cli_value is None:
        return "thinking" if config_thinking else "no-thinking"
    value = cli_value.strip().lower()
    if value in {"0", "false", "off", "no", "none", "no-thinking", "disabled"}:
        return "no-thinking"
    return "thinking"


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

    def kimicode_thinking(self, builtin: bool) -> bool:
        v = self.data.get("kimicode_thinking")
        return v if isinstance(v, bool) else builtin

    def solver_model(self, agent: str, builtin: str) -> str:
        """Model for the contract/verify solver, per agent backend."""
        return self._section("models").get(agent) or builtin

    def model_display(self, agent: str, model: str) -> str:
        """Human-readable model label for metrics; falls back to the CLI model id."""
        return self._section("model_display").get(agent) or model

    def bin(self, agent: str, builtin: str) -> str:
        return self._section("bins").get(agent) or builtin

    def eval_num(self, key: str, builtin: int) -> int:
        v = self._section("eval").get(key)
        return v if isinstance(v, int) else builtin

    def default_model(self, agent: str, builtin: str) -> str:
        """Default model for non-solver single-stage runs, per agent backend."""
        return self._section("models").get(agent) or builtin

    def timeout(self, stage: str, builtin: int) -> int:
        """Per-stage wall-clock budget (seconds): contract/eval/verify."""
        v = self._section("timeouts").get(stage)
        return v if isinstance(v, int) else builtin


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

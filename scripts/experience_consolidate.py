#!/usr/bin/env python3
"""Final experience-consolidation unit for the C/QCP flow."""
from __future__ import annotations

from dataclasses import dataclass, field
import datetime as dt
import hashlib
import os
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import agent_loop


REPO_ROOT = Path(__file__).resolve().parents[1]
GENERAL_DIR = REPO_ROOT / "experiences" / "general"
DEFAULT_SKILL = REPO_ROOT / "skills" / "consolidate" / "SKILL.md"

SCOPE_FILES: dict[str, list[str]] = {
    "contract": ["CONTRACT/README.md", "EVAL/README.md", "AUDIT/README.md"],
    "verify": [
        "SYMEXEC/README.md",
        "ASSERTION/README.md",
        "INV/README.md",
        "PROOF/README.md",
        "COMPILE/README.md",
        "AUDIT/README.md",
    ],
    "all": [
        "CONTRACT/README.md",
        "EVAL/README.md",
        "SYMEXEC/README.md",
        "ASSERTION/README.md",
        "INV/README.md",
        "PROOF/README.md",
        "COMPILE/README.md",
        "AUDIT/README.md",
    ],
}


@dataclass
class ConsolidateResult:
    changed: list[str] = field(default_factory=list)
    ran: bool = False
    detail: str = "skipped"


def snapshot() -> dict[str, str]:
    snap: dict[str, str] = {}
    if not GENERAL_DIR.exists():
        return snap
    for path in sorted(GENERAL_DIR.rglob("*")):
        if path.is_file():
            snap[path.relative_to(GENERAL_DIR).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    return snap


def changed_files(before: dict[str, str]) -> list[str]:
    after = snapshot()
    return sorted(name for name, digest in after.items() if before.get(name) != digest)


def _build_env(logs_dir: Path) -> dict[str, str]:
    env = os.environ.copy()
    for name, dirname in {
        "XDG_CACHE_HOME": ".consolidate_cache",
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


def build_prompt(scope: str, workspaces: list[Path]) -> str:
    files = SCOPE_FILES.get(scope, SCOPE_FILES["all"])
    file_list = "\n".join(f"- `experiences/general/{f}`" for f in files)
    ws_list = "\n".join(f"- `{w}`" for w in workspaces) or "- (none)"
    return f"""Use this skill as the complete workflow:
{DEFAULT_SKILL}

Dynamic context:
- Flow: `C/QCP`
- Scope: `{scope}`
- Date for new entries: `{dt.date.today().isoformat()}`

Workspaces:
{ws_list}

Relevant experience docs:
{file_list}
"""


def consolidate(
    *,
    scope: str,
    workspaces: list[Path],
    logs_dir: Path,
    agent: str = "codex",
    codex_bin: str = "codex",
    claude_bin: str = "claude",
    model: str = "",
    reasoning_effort: str = "medium",
    timeout_seconds: int = 600,
    dry_run: bool = False,
) -> ConsolidateResult:
    if dry_run:
        return ConsolidateResult(ran=False, detail="dry run; consolidation skipped")

    before = snapshot()
    logs_dir.mkdir(parents=True, exist_ok=True)
    env = _build_env(logs_dir)
    prompt = build_prompt(scope, workspaces)
    (logs_dir / "consolidate_prompt.txt").write_text(prompt, encoding="utf-8")

    exit_code, timed_out = agent_loop.run_agent_round(
        agent=agent,
        codex_bin=codex_bin,
        claude_bin=claude_bin,
        model=model,
        reasoning_effort=reasoning_effort,
        prompt=prompt,
        stdout_jsonl=logs_dir / "consolidate_stdout.jsonl",
        stderr_log=logs_dir / "consolidate_stderr.log",
        last_message_path=logs_dir / "consolidate_last_message.txt",
        env=env,
        timeout_seconds=timeout_seconds,
    )
    changed = changed_files(before)
    note = "timed out" if timed_out else f"exit {exit_code}"
    if changed:
        detail = f"consolidation ({note}) updated " + ", ".join(changed)
    else:
        detail = f"consolidation ({note}) found no general lesson; left experiences/general unchanged"
    return ConsolidateResult(changed=changed, ran=True, detail=detail)

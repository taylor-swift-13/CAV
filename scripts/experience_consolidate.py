#!/usr/bin/env python3
"""Final experience-consolidation unit for a Java/OpenJML flow.

Experience is no longer captured per agent. Instead a single consolidation agent
runs once at the very end of whatever flow ran, and *what* it consolidates
depends on the flow scope:

  * ``contract`` flow  -> contract + eval lessons.
  * ``verify``   flow  -> verify + audit lessons.
  * ``all`` (end-to-end) -> everything.

The agent reads the run's workspace logs, extracts only the **general, reusable**
lessons, and merges them into the relevant ``experiences/general/*.md`` files.
Experience is organized PER-ENTRY (逐条): each file is a list of numbered,
self-contained entries (``## N. <title>``) with a scope header and a symptom
index, after the reference design in QCP_examples/CAV/doc/experiences. A new
lesson is the next ``## N.`` entry; a correction edits the matching entry in
place. Each entry must be very detailed. If this run taught nothing general, it
is allowed to leave everything unchanged.

This module reuses the Codex invocation helper in :mod:`agent_loop`.
"""
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

SCOPE_FILES: dict[str, list[str]] = {
    "contract": ["CONTRACT.md", "EVAL.md", "OPENJML.md", "AUDIT.md"],
    "verify": ["INV.md", "ASSERTION.md", "LEMMA.md", "OPENJML.md", "AUDIT.md"],
    "all": ["CONTRACT.md", "EVAL.md", "INV.md", "ASSERTION.md", "LEMMA.md",
            "OPENJML.md", "AUDIT.md"],
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
    file_list = ", ".join(f"`experiences/general/{f}`" for f in files)
    ws_list = "\n".join(f"  - `{w}`" for w in workspaces) or "  - (none)"
    return f"""You are the final experience-consolidation agent for a Java/OpenJML
`{scope}` flow. Experience for this whole flow is accumulated here, once, at the
end. What you consolidate is scoped to the `{scope}` flow.

Read the logs of the workspaces this flow produced:
{ws_list}

In each, look at `logs/metrics.md`, `logs/issues.md`, the reasoning logs
(`reasoning.md` / `annotation_reasoning.md` / `test_reasoning.md`),
`logs/final_result.md`, `logs/continue.md`, `logs/summary.md`, and any
`openjml_*.log`, `wellformed_*.log`, `audit/findings.md`.

Then decide whether this run taught any **general, reusable** lesson, and if so
merge it into the most relevant file(s) under `experiences/general/` (for this
scope, usually: {file_list}). The experience base is plain markdown documents.

What counts as experience — STRICT:
- It MUST be GENERAL: a rule, pattern, or pitfall that will help on *other*
  tasks. Examples: a JML/OpenJML feature that is unsupported and its workaround;
  an invariant/assertion/lemma shape that discharges a class of obligations; an
  anti-cheating pattern; a class of spec/impl disagreement and how to spot it.
- It MUST NOT be task-specific. Do not record "for `array_count_even` I wrote
  X". Strip the task identity; keep the transferable rule. (You may cite the task
  once as the *origin* of a general rule, but the rule itself must stand alone.)
- If this run only re-applied already-documented patterns and taught nothing
  new and general, **do not write anything** — leaving `experiences/general/`
  unchanged is a valid, expected outcome. Do not pad with dated "confirmation"
  lines or restate existing notes.

Organization — experience is PER-ENTRY (逐条). Each file is a list of numbered,
individually-addressable entries shaped like:

    # <Topic> Experience

    <one-paragraph scope header: what THIS file records and what it does not,
     pointing to sibling files for the rest>

    常见入口 / symptom index:
    - <symptom> -> see N
    - <symptom> -> see M

    ## 1. <short imperative rule title>
    <very detailed body>

    ## 2. <short imperative rule title>
    ...

Adding/updating a lesson:
- Add it as the NEXT sequential numbered entry (`## N. <title>`) in the most
  relevant file. Each entry stands alone and is referenced by its number.
- If a matching rule already exists, EDIT THAT NUMBERED ENTRY IN PLACE to sharpen
  or correct it — do not append a near-duplicate (reference rule: "对已有规则做
  更正时直接改原条目").
- If the file has a symptom index at the top, add a `<symptom> -> see N` line for
  your new entry so it is discoverable.
- Also add a `<symptom> -> <FILE>.md N` line to the global symptom index in
  `experiences/general/README.md` (section "按症状检索") for the new entry.
- Preserve the file's scope header and existing numbering.

Each entry must be VERY DETAILED — include all of:
- a short imperative title;
- the trigger / symptom: the exact diagnostic class and message
  (e.g. `NOT IMPLEMENTED ... \\num_of`, `Postcondition`, `ArithmeticOperationRange`,
  `LoopInvariant`, an anti-cheating finding), and where it surfaces (stage, the
  command that produced it);
- the root cause / mechanism: WHY it happens, in terms of how OpenJML / the SMT
  backend / JML semantics work;
- the general rule: what to do instead, stated so it applies beyond this task;
- a concrete, minimal code/spec snippet showing the fix shape;
- scope of applicability: when this applies and when it does not.

Hard rules:
- Touch nothing outside `experiences/general/`. Do not edit code, specs, or
  workspace files. Do not use assume/axiom/skipesc/nowarn in any example.
- Writing zero changes is allowed when there is no general lesson.
Date any new entries {dt.date.today().isoformat()}.
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
        # No change is a legitimate outcome: nothing general to record.
        detail = f"consolidation ({note}) found no general lesson; left experiences/general unchanged"
    return ConsolidateResult(changed=changed, ran=True, detail=detail)

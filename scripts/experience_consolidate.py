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
    "contract": ["CONTRACT/README.md", "EVAL/README.md", "OPENJML/README.md", "AUDIT/README.md"],
    "verify": ["INV/README.md", "ASSERTION/README.md", "LEMMA/README.md", "OPENJML/README.md", "AUDIT/README.md"],
    "all": ["CONTRACT/README.md", "EVAL/README.md", "INV/README.md", "ASSERTION/README.md", "LEMMA/README.md",
            "OPENJML/README.md", "AUDIT/README.md"],
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

In each workspace, inspect at least:
- `logs/metrics.md`
- `logs/issues.md`
- `logs/final_result.md`
- reasoning logs such as `reasoning.md`, `annotation_reasoning.md`,
  `test_reasoning.md`, `continue.md`, `summary.md`
- `openjml_*.log`, `wellformed_*.log`, `audit/findings.md` when present

For **efficiency lessons** specifically, also inspect
`logs/agent_stdout_*.jsonl` (the upstream stage agent's harness transcript).
**Do not** read these files sequentially in full — they may be megabytes and
will burn context. Use targeted lookups:
- `grep -c '"type":"tool_use"' logs/agent_stdout_*.jsonl` → total tool calls;
  unusually high counts on a "simple" task indicate flailing.
- Group repeated tool calls (e.g. many similar `grep`s for the same spec
  keyword or method name) — this is the signature of an agent hunting for
  something that doesn't exist or that it doesn't know how to find.
- Look at the longest stretches between progress markers (file writes,
  `openjml` invocations) to find dead-ends.
- Compare attempts when `Attempts > 1`: what was the first attempt's blocker,
  and what was the actual fix?

The curated `issues.md` / reasoning logs often miss this self-aware view — the
agent doesn't usually realize it spent 95 calls finding a spec keyword that
doesn't exist. The jsonl is where that lesson lives.

Then decide whether this run taught any **general, reusable** lesson and where
it belongs. For this scope the relevant docs are: {file_list}.

What counts as experience — STRICT:
- It MUST be GENERAL: a rule, pattern, or pitfall that will help on *other*
  tasks. Examples: a JML/OpenJML feature that is unsupported and its workaround;
  an invariant/assertion/lemma shape that discharges a class of obligations; an
  anti-cheating pattern; a class of spec/impl disagreement and how to spot it.
- It MUST NOT be task-specific. Do not record "for `array_count_even` I wrote X".
  Strip the task identity; keep the transferable rule. (You may cite the task
  once as the *origin* of a general rule, but the rule itself must stand alone.)
- If this run only re-applied already-documented patterns, **do not write
  anything** — leaving `experiences/general/` unchanged is a valid outcome.

Each `experiences/general/<NAME>/` doc has two retrieval surfaces with
**independent numbering**. Universal and topical entries do NOT share a counter.

| Surface | Where it lives | How agents find it |
|---------|----------------|--------------------|
| **Universal** | `<NAME>/README.md` as `## <U>. <title>` sections | The README's 「常见入口」/ symptom index at the top of the file (human-browsed) |
| **Topical** | `<NAME>/<N>/<slug>.md` + `<NAME>/<N>/<slug>.fingerprint` (one per numbered subfolder) | `scripts/search_fingerprint.py` matches `keywords` + `semantic_description` and returns the `.md` path |

`<U>` (README section counter) and `<N>` (folder counter) are completely
**independent integer sequences**. README's largest § might be 12 while the
folder counter is at 5; that's fine. When you add a universal entry, only
increment `<U>`. When you add a topical entry, only increment `<N>`.

Decide universal vs topical by asking: "does this lesson apply only to a
particular shape of problem (e.g. a specific JML construct like `\\num_of`, a
specific data structure like array, a specific diagnostic class like
`ArithmeticOperationRange`), or to every problem in this stage?" If it's
clearly problem-class-specific → topical (numbered subfolder + fingerprint).
If uncertain → default to universal (a section in README.md).

**To add a universal entry**:

1. Open `<NAME>/README.md` and read the existing `## <U>. ...` headings.
2. Append a new `## <max_U + 1>. <Short title> (<date>)` at the bottom.
3. Add a one-line bullet to the「常见入口」/ symptom index at the top of the
   same file so readers can find it by symptom. Also add a
   `<symptom> -> <NAME>/README.md N` line to the global symptom index in
   `experiences/general/README/README.md` ("按症状检索" section).

**To add a topical entry**:

1. `ls experiences/general/<NAME>/` and find the largest existing numeric
   subfolder name (ignore `README.md`). Call it `M`. If none exists, `M = 0`.
2. Create `experiences/general/<NAME>/<M+1>/` (the new folder).
3. Inside, write exactly two sibling files: `<slug>.md` (content) and
   `<slug>.fingerprint` (JSON below). `<slug>` is kebab-case derived from the
   title; the number `<M+1>` is the opaque accumulator ID.
4. Do NOT add a symptom-index entry for topical experiences — they are
   retrieved by fingerprint, not by README browsing.

**Topical entry format**:

`<NAME>/<N>/<slug>.md`:
```
# <Short title>

<body — self-contained; an agent retrieving this should be able to act on it
without reading the README.md>
```

`<NAME>/<N>/<slug>.fingerprint` (JSON, two fields):
```json
{{
  "semantic_description": "<1-2 sentence summary of when this applies>",
  "keywords": {{
    "problem_kind": "<one of experiences/INDEX.md controlled vocab>",
    "data": "<one of experiences/INDEX.md controlled vocab>",
    "pattern": "<one of experiences/INDEX.md controlled vocab>"
  }}
}}
```

A keyword value may be an array if the experience covers multiple classes.

Each entry (universal or topical) must be VERY DETAILED — include all of:
- a short imperative title;
- the trigger / symptom: exact diagnostic class and message
  (e.g. `NOT IMPLEMENTED ... \\num_of`, `Postcondition`,
  `ArithmeticOperationRange`, `LoopInvariant`, an anti-cheating finding) and
  where it surfaces (stage, the command that produced it);
- the root cause / mechanism: WHY, in terms of OpenJML / SMT backend /
  JML semantics;
- the general rule: what to do instead, stated so it applies beyond this task;
- a concrete, minimal code/spec snippet showing the fix shape;
- scope of applicability: when this applies and when it does not.

Capture TWO kinds of reusable lesson:
1. Correctness — how to produce a result that actually verifies.
2. Efficiency — what made this run slow or wasteful, and the reusable shortcut
   that avoids it next time. File on the same surface as the topic.

Hard rules:
- Touch nothing outside `experiences/general/`. Do not edit code, specs, or
  workspace files. Do not use assume/axiom/skipesc/nowarn in any example.
- Only record reusable rules, not task-specific anecdotes.
- If an existing rule in README.md or a topical entry should be sharpened,
  edit it in place instead of appending a near-duplicate.
- Writing zero changes is allowed when there is no general lesson.
- Date any new entries {dt.date.today().isoformat()}.
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

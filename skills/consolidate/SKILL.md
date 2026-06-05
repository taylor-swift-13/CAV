---
name: c-qcp-consolidate
description: Consolidate reusable experience from completed C/QCP contract, verify, eval, or end-to-end workspaces into experiences/general.
---

# C/QCP Consolidation

Use this skill only at the end of a runner flow. The runner prompt provides
the flow, scope, date, workspace list, and relevant `experiences/general`
documents. Consolidation writes only durable, reusable lessons; it never edits
task workspaces, inputs, raw problems, or runner code.

## Evidence To Read

For each workspace, inspect:

- `logs/metrics.md`, `logs/issues.md`, `logs/final_result.md`;
- reasoning logs such as `reasoning.md`, `annotation_reasoning.md`,
  `proof_reasoning.md`, `test_reasoning.md`, and `continue.md`;
- compile, replay, syntax-check, audit-check, symexec, and Coq logs when
  present.

For efficiency lessons, inspect upstream `logs/agent_stdout_*.jsonl` with
targeted searches only. Count tool calls, group repeated searches, compare
attempts, and look for long stretches without meaningful progress. This is an
exception for upstream stage transcripts; do not inspect the current
consolidation run's transcript.

## What Counts

Record a lesson only when it generalizes to future problems. Useful lessons
include QCP contract shape, valid `proof_auto.v` or `proof_manual.v` patterns,
loop invariant and assertion placement, Coq proof obligations, syntax or
wellformedness pitfalls, deterministic audit failures, and workflow shortcuts
that avoid retries.

Capture both:

- correctness: what makes the result verify without cheating;
- efficiency: what made the run slow and the reusable shortcut that avoids it.

If the run only reused known patterns, leave `experiences/general/` unchanged.

## Retrieval Surfaces

Each `experiences/general/<NAME>/` area has two independent surfaces.

Universal entries live in `<NAME>/README.md` as numbered sections:

```markdown
## <U>. <Short title> (<date>)
```

Topical entries live in numbered subfolders:

```text
<NAME>/<N>/<slug>.md
<NAME>/<N>/<slug>.fingerprint
```

The README section counter `<U>` and topical folder counter `<N>` are
independent. Increment only the counter for the surface you are adding to.

Use a universal README entry for stage-wide rules. Use a topical entry for a
specific problem class, data structure, algorithm shape, or recurring proof
shape. If uncertain, prefer a universal entry.

## Universal Entry Rules

1. Read existing `## <U>. ...` headings in the target README.
2. Append `## <max_U + 1>. <Short title> (<date>)`.
3. Add a one-line topic entry to the README's top index.
4. Never store a new lesson by changing an old heading date. Edit an existing
   section only to correct, tighten, or merge a true duplicate.

## Topical Entry Rules

1. Find the largest numeric subfolder in `experiences/general/<NAME>/`; use
   `0` if none exists.
2. Create `<NAME>/<M+1>/`.
3. Add exactly two sibling files: `<slug>.md` and `<slug>.fingerprint`.
4. `<slug>.fingerprint` must be the exact JSON copied from the relevant
   workspace's `logs/workspace_fingerprint.json`. Keep its original
   `semantic_description` and `keywords`; do not invent, summarize, or
   reclassify them.
5. Do not add README index entries for topical files.

Topical markdown format:

```markdown
# <Short title>

<self-contained reusable rule, with the symptom, cause, rule, minimal snippet
or command shape, and scope of applicability>
```

## Hard Rules

- Touch only `experiences/general/`.
- Record reusable rules, not task-specific anecdotes.
- Date every new entry with the date supplied by the runner prompt.
- Write zero changes when there is no general lesson.
- Do not introduce examples that rely on `assume`, `axiom`, admitted proofs, or
  bypassing deterministic checks.

---
name: java-openjml-consolidate
description: Consolidate reusable experience from completed Java/OpenJML contract, verify, audit, eval, or end-to-end workspaces into experiences/general.
---

# Java/OpenJML Consolidation

Use this skill only at the end of a runner flow. The runner prompt provides
the flow, scope, date, workspace list, and relevant `experiences/general`
documents. Consolidation writes only durable, reusable lessons; it never edits
task workspaces, inputs, raw problems, or runner code.

## Evidence To Read

For each workspace, inspect:

- `logs/metrics.md`, `logs/issues.md`, `logs/final_result.md`;
- reasoning logs such as `reasoning.md`, `annotation_reasoning.md`,
  `test_reasoning.md`, `summary.md`, and `continue.md`;
- `openjml_*.log`, `wellformed_*.log`, `audit/findings.md`, and deterministic
  scan logs when present.

For efficiency lessons, inspect upstream `logs/agent_stdout_*.jsonl` with
targeted searches only. Count tool calls, group repeated searches, compare
attempts, and look for long stretches without meaningful progress. This is an
exception for upstream stage transcripts; do not inspect the current
consolidation run's transcript.

## What Counts

Record a lesson only when it generalizes to future problems. Useful lessons
include JML/OpenJML unsupported features and workarounds, invariant/assertion
or lemma shapes that discharge a class of obligations, anti-cheating findings,
spec/implementation disagreement patterns, deterministic scan failures, and
workflow shortcuts that avoid retries.

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
specific problem class, data structure, JML construct, OpenJML diagnostic, or
recurring proof shape. If uncertain, prefer a universal entry.

## Universal Entry Rules

1. Read existing `## <U>. ...` headings in the target README.
2. Append `## <max_U + 1>. <Short title> (<date>)`.
3. Add a one-line symptom/topic entry to the target README's top index.
4. Add a matching `<symptom> -> <NAME>/README.md <U>` line to
   `experiences/general/README/README.md` when that global index exists.
5. Never store a new lesson by changing an old heading date. Edit an existing
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
5. Do not add README or global-index entries for topical files.

Topical markdown format:

```markdown
# <Short title>

<self-contained reusable rule, with the symptom, cause, rule, minimal snippet
or command shape, and scope of applicability>
```

## Entry Detail

For universal or topical entries, include the trigger or symptom, where it
surfaced, the OpenJML/JML mechanism, the general rule, a minimal code/spec
shape when useful, and the scope where the rule applies.

## Hard Rules

- Touch only `experiences/general/`.
- Record reusable rules, not task-specific anecdotes.
- Date every new entry with the date supplied by the runner prompt.
- Write zero changes when there is no general lesson.
- Do not introduce examples that rely on `assume`, `axiom`, `skipesc`,
  `nowarn`, unchecked native lemmas, broad frame clauses, or suppressions.

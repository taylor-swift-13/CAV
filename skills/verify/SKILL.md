---
name: java-openjml-verify
description: Verify Java/JML source with Codex-assisted OpenJML iteration.
---

Use this workflow for the Java/OpenJML verify stage. This skill consumes an
existing Java implementation/spec and repairs only the verified working copy
until OpenJML ESC passes without cheating.

## Exit Discipline

Verify is a long iterative task. Do **not** end the current agent run merely
because OpenJML, the anti-cheating scanner, fingerprint validation, or a local
helper proof reports a concrete repairable blocker. If the blocker can be fixed
by editing the verified working Java file or current workspace logs, keep
running the loop: edit one focused thing, rerun the relevant gate, inspect the
first remaining failure, and edit again.

Only write `Final Result: Fail` and exit when one of these is true:

- the original Java contract/implementation is missing, contradictory, or needs
  a Contract-stage/user decision;
- the current verification condition is genuinely unprovable under the allowed
  write boundary, and the missing premise or semantic contradiction is recorded;
- continuing would require editing files outside the verified working Java file
  or current workspace logs;
- the external timeout is close enough that another meaningful edit/gate cycle
  cannot complete;
- all feasible in-scope repairs are exhausted and a deterministic runner gate
  still fails for a reason that cannot be advanced in this workspace.

Ordinary OpenJML diagnostics, scanner findings that point to a specific allowed
edit, missing fingerprint fields, failed loop invariants, arithmetic range
failures, nullness/bounds failures, and helper-method proof failures are not
exit reasons. They are the next work item for the same run.


跨阶段共用规则（读写边界、效率、experiences 只读、reasoning log、`Final Result` 格式）见 `skills/COMMON.md`。本文件只描述本阶段特有内容。

## Pipeline Position

This is the final proof stage of the Java/OpenJML workflow.

Input:

- `input/<name>.java`

Output:

- `output/verify_<timestamp>_<name>/original/<name>.java`
- `output/verify_<timestamp>_<name>/verified/<name>.java`
- `output/verify_<timestamp>_<name>/logs/workspace_fingerprint.json`
- `output/verify_<timestamp>_<name>/logs/annotation_reasoning.md`
- `output/verify_<timestamp>_<name>/logs/issues.md`
- `output/verify_<timestamp>_<name>/logs/metrics.md`
- runtime OpenJML and scanner logs under the same workspace logs directory.

Command shape:

```bash
python3 scripts/run_verify.py input/<name>.java --class-name <ClassName>
```

On success, the runner exports a CAV-style compact example snapshot under
`experiences/end-end/<name>/` with only:

- `original/<name>.java`
- `verified/<name>.java`
- `logs/workspace_fingerprint.json`
- `logs/annotation_reasoning.md`
- `logs/issues.md`

`experiences/end-end` exports stable source/proof artifacts and curated
reasoning summaries. Runtime-only logs such as Codex stdout/stderr, OpenJML
stdout/stderr, scanner stdout/stderr, and metrics stay in the workspace logs.

## Inputs

- Original input Java file.
- Verified working Java file.
- Workspace path.
- Class name.

## Required References

Read these local references before making verification edits:

- `/home/yangfp/CAV-JAVA/experiences/general/README/README.md` (experience entry; jump by symptom)
- `/home/yangfp/CAV-JAVA/experiences/general/INV/README.md`
- `/home/yangfp/CAV-JAVA/experiences/general/ASSERTION/README.md`
- `/home/yangfp/CAV-JAVA/experiences/general/LEMMA/README.md`
- `/home/yangfp/CAV-JAVA/experiences/general/AUDIT/README.md`
- `/home/yangfp/CAV-JAVA/experiences/general/OPENJML/README.md`
- `/home/yangfp/CAV-JAVA/experiences/INDEX.md`

Search completed end-to-end examples before making verification edits:

- `/home/yangfp/CAV-JAVA/experiences/end-end`

Use prior examples as concrete evidence for successful Java/JML patterns,
workspace layout, fingerprint format, and issue-log style. Prefer examples with
similar control flow, data type, or OpenJML diagnostic. Record the selected
example path in `logs/annotation_reasoning.md` when it informs a change.

Useful commands:

```bash
find /home/yangfp/CAV-JAVA/experiences/end-end -maxdepth 4 -type f | sort
rg -n "requires|ensures|assignable|loop_invariant|assert|pure|Final Result|workspace_fingerprint" /home/yangfp/CAV-JAVA/experiences/end-end
```

Before OpenJML success can be reported, update
`logs/workspace_fingerprint.json` so:

- `semantic_description` is non-empty;
- `keywords` is non-empty;
- every `keywords` key and value comes from
  `/home/yangfp/CAV-JAVA/experiences/INDEX.md`;
- no free-form synonym is invented.

Use these official OpenJML resources as the local reference corpus:

- `/home/yangfp/CAV-JAVA/doc`
- `/home/yangfp/CAV-JAVA/doc/openjml-tutorial`
- `/home/yangfp/CAV-JAVA/doc/openjml-documentation`
- `/home/yangfp/CAV-JAVA/doc/openjml-specs`
- `/home/yangfp/CAV-JAVA/examples`
- `/home/yangfp/CAV-JAVA/examples/openjml-tutorial`
- `/home/yangfp/CAV-JAVA/examples/openjml-demos`
- `/home/yangfp/CAV-JAVA/examples/openjml-userguide`

Search `doc` and `examples` selectively. Useful queries include:

```bash
rg -n "loop_invariant|decreases|assignable|assert|pure|model|ghost|spec_public" /home/yangfp/CAV-JAVA/doc /home/yangfp/CAV-JAVA/examples
rg -n "ArithmeticOperationRange|InvariantExit|Precondition|PossiblyNull|LoopInvariant" /home/yangfp/CAV-JAVA/doc /home/yangfp/CAV-JAVA/examples
```

## Boundaries

- Modify only the verified working Java file and files under the current
  workspace logs.
- Treat the original input Java file as read-only baseline evidence.
- Preserve baseline `requires`, `ensures`, and `assignable` clauses in their
  original strength and reachability.
- Keep the implementation semantically aligned with the input. If the input
  implementation/spec is fundamentally wrong, record the issue and fail the
  verify stage instead of silently changing the problem.

## Verification Aids

Allowed aids:

- `loop_invariant` clauses.
- `decreases` clauses.
- JML `assert` statements used as local bridge facts.
- Verified `pure` helper methods with executable bodies.
- `spec_public`, model fields, or ghost state only when needed and documented.

Forbidden aids:

- `assume`.
- `axiom`.
- `skipesc`.
- broad `nowarn`.
- `native` helpers.
- reflection.
- impossible preconditions.
- unreachable-path tricks.

## Iteration Procedure

1. Read the original Java and the verified working Java.
2. Run anti-cheating scan before edits:

   ```bash
   scripts/check_jml_cheating.py --baseline <original> <verified>
   ```

3. Run OpenJML:

   ```bash
   scripts/run_openjml_verify.sh <verified>
   ```

4. Classify the first concrete OpenJML failure:
   - arithmetic overflow or range proof;
   - nullness or array bounds;
   - missing `assignable`;
   - loop invariant initialization;
   - loop invariant preservation;
   - loop exit not strong enough;
   - visibility/spec-public issue;
   - helper lemma/pure method issue;
   - anti-cheating violation.
5. Search `/home/yangfp/CAV-JAVA/experiences/end-end` first for a similar
   completed task, then search `/home/yangfp/CAV-JAVA/doc` and
   `/home/yangfp/CAV-JAVA/examples`
   for the closest OpenJML pattern before editing.
6. Append to `logs/annotation_reasoning.md` before changing annotations. Include:
   - command that failed;
   - exact OpenJML message;
   - file and line;
   - local code/spec snippet;
   - selected reference path from `doc` or `examples`, when used;
   - planned invariant/assertion/lemma change;
   - why the change follows from the program state.
7. Edit only the verified Java file.
8. Rerun anti-cheating scan and OpenJML.
9. Repeat until both pass or the blocker satisfies `Exit Discipline`.

## Invariant Rules

- Every loop needs enough facts for initialization, preservation, and exit.
- Track loop bounds explicitly.
- Track modified and unmodified array regions separately.
- Track accumulators as prefix or segment facts.
- Add `decreases` when OpenJML cannot prove termination.
- Facts that must hold across iterations belong in loop invariants; assertions
  are for facts derivable at a specific program point.

## Assertion Rules

- Use JML `assert` only for facts derivable at that program point.
- Prefer assertions for branch facts, arithmetic bounds, and loop-exit bridges.
- Direct postcondition assertions are appropriate only when current invariants
  and branch facts already imply them.
- Assertions must be checked by OpenJML from the current proof context.

## Lemma Rules

- Helper lemmas must be Java/JML artifacts OpenJML can check.
- Prefer small `pure` methods with executable bodies and contracts.
- Helper lemmas use executable bodies, reachable preconditions, and checked
  model/pure methods.
- If a helper lemma is added, OpenJML must verify it in the same run as the
  target class.

## Logs

Maintain these logs in the workspace:

- `logs/annotation_reasoning.md`
- `logs/issues.md`
- `logs/metrics.md`

`logs/issues.md` must record every representative blocker with:

- stage;
- command;
- failing file and line;
- OpenJML message;
- diagnosis;
- edit made;
- result after rerun.

`logs/metrics.md` must end with one of:

```text
Final Result: Success
Final Result: Fail
```

## Completion

Success requires all of the following:

- `scripts/check_jml_cheating.py --baseline <original> <verified>` exits 0.
- `scripts/run_openjml_verify.sh <verified>` exits 0.
- No forbidden proof aid remains in the verified Java file.
- Baseline contract clauses are preserved.
- Logs are complete.
- `logs/workspace_fingerprint.json` has a non-empty `semantic_description` and
  controlled `keywords` from `/home/yangfp/CAV-JAVA/experiences/INDEX.md`.

Do **not** record experience yourself. Experience is consolidated once at the
very end of the flow by a dedicated unit (`scripts/experience_consolidate.py`).
Write clear `logs/issues.md`, `logs/annotation_reasoning.md`,
`logs/continue.md`, and `logs/summary.md` — the consolidation unit reads them.

If any condition is missing, first apply `Exit Discipline`: continue fixing any
repairable blocker in the same run. Write `Final Result: Fail` only for a
genuinely out-of-scope, unprovable, or timeout-limited blocker.

## Iteration / Restart / Resume

The verify runner (`run_verify.py`) drives this stage in a budget-driven
loop (`scripts/agent_loop.py`):

- Keep iterating in the **same workspace** until OpenJML ESC and the
  anti-cheating scan both pass, or the time budget is exhausted. A fresh round
  starts only if you exit early without passing; a round that hits its timeout
  is a failure and is **not** restarted.
- On every round before editing, append a fresh section to `logs/continue.md`
  (never overwrite): why the previous round did not finish, the current blocker,
  next step and plan, citing concrete evidence (file:line, the exact OpenJML
  message, the JML/Java snippet).
- At the end of each round write `logs/summary.md`: what you did, current proof
  state, and where you are stuck — the next round resumes from it.
- When re-entered with `Restart feedback`, the feedback is in the latest
  restart-feedback section of `logs/continue.md`; read it and fix the cited
  verify blocker without weakening the spec.


## 条件性 mode addendum

runner 在 prompt 加标记触发以下附录，**没标记就不读**。多个标记可叠加。

| Prompt 标记 | 附录文件 | 含义 |
|------------|---------|------|
| `Attempt: N (retry — ...)` 且 N > 1 | `MODE_RETRY.md` | 接力上一轮工作，必须追加 `logs/continue.md` 新 section |
| `Restart feedback` 块 | `MODE_RERUN_AUDIT.md` | audit agent 反馈后的 verify 重跑，逐条修复 finding |

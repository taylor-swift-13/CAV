---
name: java-openjml-contract
description: Produce Java source with JML contracts from raw task text.
---

Use this workflow for the Java/OpenJML contract stage.

## Pipeline Position

This is stage 1 of the Java/OpenJML workflow.

Input:

- `raw/<name>.md`

Output:

- `input/<name>.java`
- `output/contract_<timestamp>_<name>/logs/reasoning.md`
- `output/contract_<timestamp>_<name>/logs/issues.md`
- `output/contract_<timestamp>_<name>/logs/metrics.md`

Command shape:

```bash
python3 scripts/run_contract.py raw/<name>.md --function-name <method_or_class>
```

The next normal stage is verify. In the pipeline entrypoints, the default flow
is `contract -> verify`; pass `--eval` to enable the eval critic between them,
and pass `--audit` later if you also want the verify critic.

## Read First

- `experiences/general/README.md` (experience entry; jump by symptom)
- `experiences/general/CONTRACT.md`
- `experiences/general/AUDIT.md`

## Search Prior Examples

Before writing the Java file, search completed examples under
`/home/yangfp/CAV-JAVA/experiences/end-end`.

Use the existing examples as concrete patterns for class layout, JML clause
style, anti-cheating-safe specifications, and workspace log expectations. Do
not copy an unrelated example blindly; cite the closest example path in
`logs/reasoning.md` when one influenced the contract.

Useful commands:

```bash
find /home/yangfp/CAV-JAVA/experiences/end-end -maxdepth 3 -type f | sort
rg -n "requires|ensures|assignable|loop_invariant|assert|pure" /home/yangfp/CAV-JAVA/experiences/end-end
```

## Inputs

- Raw markdown path.
- Target function or class name.
- Output Java path.
- Workspace path.

## Rules

- Write `logs/reasoning.md` before creating or changing the output Java file.
- Generate a single Java file with Java implementation and JML contract.
- Include `requires`, `ensures`, and `assignable`.
- Do not add loop invariants, assertions, assumptions, axioms, suppressions, or
  unchecked helpers in the contract stage.
- If a helper is necessary, make it pure, executable, and specified.
- The spec must be **well-formed under OpenJML**: it must parse and type-check,
  and it must use only verifier-supported features. Do **not** use the
  aggregate quantifiers `\num_of`, `\sum`, or `\product`, or any feature OpenJML
  reports as `NOT IMPLEMENTED` — these compile but make the contract unprovable
  downstream. Express count/sum results with a `pure` recursive helper instead
  (see `CONTRACT.md`). The contract stage runs
  `scripts/check_spec_wellformed.py` and **fails** on parse/type errors or
  unsupported features. It does **not** require every verification condition to
  discharge — undischarged `Postcondition`/`Invariant`/`Assert`/loop obligations
  are expected here and are the verify stage's job.
- Self-check before finishing:
  `python3 scripts/check_spec_wellformed.py input/<name>.java`. Exit 0 means
  well-formed (VCs may remain open); exit 1 means a fatal spec problem you must
  fix now, not defer to verify.
- Do **not** record experience yourself. Experience is consolidated once at the
  very end of the flow by a dedicated unit (`scripts/experience_consolidate.py`).
  Just write clear `logs/reasoning.md`, `logs/issues.md`, `logs/continue.md`, and
  `logs/summary.md` — the consolidation unit reads them.

## Iteration / Restart / Resume

The contract runner (`run_contract.py`) drives this stage in a
budget-driven loop (`scripts/agent_loop.py`):

- Keep iterating in the **same workspace** until the spec passes the
  anti-cheating scan and the well-formedness gate, or the time budget is
  exhausted. The loop restarts a fresh round only if you exit early without
  passing; a round that hits its timeout is a failure and is **not** restarted.
- On every round before editing, append a fresh section to `logs/continue.md`
  (never overwrite): why the previous round did not finish, the current blocker,
  the next step and plan, citing concrete evidence (file:line, the
  well-formedness / OpenJML message, the spec snippet).
- At the end of each round write `logs/summary.md`: what you did, the current
  spec state, where you are stuck — this is what the next round resumes from.
- When re-entered after the eval critic overturned the spec, the findings are in
  the `## overturn` section of `logs/continue.md`; read it and fix exactly that.

## Completion

- `input/<name>.java` exists.
- `logs/reasoning.md`, `logs/issues.md`, and `logs/metrics.md` exist.
- `scripts/check_jml_cheating.py input/<name>.java` passes.
- `scripts/check_spec_wellformed.py input/<name>.java` exits 0 (spec parses,
  type-checks, and uses only verifier-supported features; undischarged VCs are
  allowed).
- `logs/metrics.md` ends with `Final Result: Success` only when the generated
  Java file exists, the anti-cheating scan passes, and the well-formedness gate
  passes. (Experience is consolidated separately at the end of the flow.)

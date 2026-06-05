2026-06-04 23:34:18 +0800

Phenomenon: initial replay of `coq/generated/array_count_between_goal.v` failed before any proof obligation because the generated short import `Require Import int_array_strategy_goal.` matched both `QCP_demos_LLM` and `QCP_demos_human`.

Location: `output/verify_20260604_230601v_array_count_between/coq/generated/array_count_between_goal.v:21`.

Repair action: added workspace-local wrapper modules in `output/verify_20260604_230601v_array_count_between/original/` for `int_array_strategy_*`, `uint_array_strategy_*`, `undef_uint_array_strategy_*`, and `array_shape_strategy_*`, then compiled them with `-Q "$ORIG" ""` before replaying the generated files.

Key error:

```text
Error: Required library int_array_strategy_goal matches several files in path
```

Why this fixed it: the wrapper files give each short import a unique physical file in the current workspace, so the generated Coq stays unchanged while replay path resolution becomes deterministic.

2026-06-04 23:34:18 +0800

Phenomenon: the first manual proof attempt for `proof_of_array_count_between_safety_wit_3` could not prove `count + 1 <= INT_MAX`; the VC lacked a preserved representability fact for `n`.

Location: `annotated/verify_20260604_230601v_array_count_between.c` loop entry and `coq/generated/array_count_between_proof_manual.v` safety witness.

Repair action: inserted `/*@ n <= INT_MAX by local */` before the loop and carried `n <= INT_MAX` inside the invariant, then reran `symexec` and rebuilt the proof against the fresh VC.

Key proof-state fragment:

```text
H1 : i < n_pre
H4 : count = array_count_between_spec (sublist 0 i l) lo_pre hi_pre
============================
count + 1 <= 2147483647
```

Why this fixed it: the safety obligation is about C `int` representability. The right source of the upper bound is the local `Int` store for `n`, and `by local` makes that fact available to symbolic execution instead of forcing Coq to guess a missing premise.

2026-06-04 23:34:18 +0800

Phenomenon: after rerunning `symexec`, the proof script still appeared to miss the new `n_pre <= INT_MAX` hypothesis.

Location: replay compile for `coq/generated/array_count_between_proof_manual.v`.

Repair action: deleted stale non-`.v` Coq artifacts under `output/verify_20260604_230601v_array_count_between/coq/` and rebuilt from source so `Require Import array_count_between_goal` used the freshly generated VC instead of an older `.vo`.

Key stale-artifact symptom: interactive proof states still showed the old hypothesis set even though `coq/generated/array_count_between_goal.v` on disk had the new pure facts.

Why this fixed it: `coqtop`/`coqc` load compiled `.vo` files when present. Cleaning them forced replay to consume the latest generated `.v` files and aligned the proof state with the updated annotation.

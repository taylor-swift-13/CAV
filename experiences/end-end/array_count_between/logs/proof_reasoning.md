2026-06-04 23:12:14 +0800

Phenomenon: replay compilation failed before entering any manual lemma. `coqc` stopped in `output/verify_20260604_230601v_array_count_between/coq/generated/array_count_between_goal.v` with a duplicate physical-path error on `Require Import int_array_strategy_goal`.

Location: generated file `output/verify_20260604_230601v_array_count_between/coq/generated/array_count_between_goal.v:21` during the `goal.v` compile step.

Repair action: add local short-name wrapper modules inside the current workspace so `-Q "$ORIG" ""` resolves each strategy import to a unique file, following the compile guidance for duplicate strategy libraries.

Key error:

```text
Error: Required library int_array_strategy_goal matches several files in path
```

Why this change: the failure is a load-path ambiguity, not a proof obligation. Fixing import resolution first is required before iterating on the actual witness proofs.

2026-06-04 23:12:14 +0800

Phenomenon: after import resolution was fixed, `pre_process; entailer!; try lia` discharged `entail_wit_1` but left five stable list/arithmetic goals: `safety_wit_3` needed an upper bound on the prefix count, `entail_wit_2_{1,2,3}` needed the recurrence for `sublist 0 (i + 1) l`, and `return_wit_1` needed `sublist 0 i l = l` once loop exit implies `i = n_pre`.

Location: manual lemmas in `output/verify_20260604_230601v_array_count_between/coq/generated/array_count_between_proof_manual.v`.

Repair action: add helper lemmas for `array_count_between_spec` bounds, appending one element to a prefix, and the `sublist 0 (i + 1)` decomposition; then keep each witness proof short by rewriting with those lemmas and closing the remaining arithmetic/branch contradictions.

Key remaining goals after the try-first tactic:

```text
count + 1 <= 2147483647
count + 1 = array_count_between_spec (sublist 0 (i + 1) l) lo_pre hi_pre
count = array_count_between_spec (sublist 0 (i + 1) l) lo_pre hi_pre
count = array_count_between_spec l lo_pre hi_pre
```

Why this change: these are proof-layer obligations. The witness shape is already clean and reflects the intended prefix-summary invariant, so changing annotations further would only churn the VC without reducing the real proof work.

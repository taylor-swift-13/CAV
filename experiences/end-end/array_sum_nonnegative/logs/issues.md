## Issue 1

Phenomenon: The first generated return witness quantified both current `a, n` and pre-state `a_pre, n_pre` but only assumed `IntArray.full a n l` in the loop-exit premise. That made the postcondition shape depend on recovering parameter-equality facts that were not preserved by the invariant.

Location: `array_sum_nonnegative_return_wit_1` in `/home/yangfp/CAV/C/CAV/output/verify_20260605_010426v_array_sum_nonnegative/coq/generated/array_sum_nonnegative_goal.v`, rooted in `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_010426v_array_sum_nonnegative.c`.

Fix action: Strengthened the loop invariant with `a == a@pre` and `n == n@pre`, then cleared and regenerated all generated Coq files with a fresh `symexec` run.

Key fragment:

```c
a == a@pre &&
n == n@pre &&
```

Why this fixed it: The function is a read-only scan, so the pointer and length are stable across the loop. Keeping those facts in the invariant made the regenerated witnesses use `a_pre` and `n_pre` consistently instead of requiring an impossible proof bridge.

## Issue 2

Phenomenon: The first full `coqc` replay failed before manual proofs were checked because `array_sum_nonnegative_goal.v` imported short strategy module names that matched both `QCP_demos_LLM` and `QCP_demos_human`.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_010426v_array_sum_nonnegative/coq/generated/array_sum_nonnegative_goal.v`, compile failure `Required library int_array_strategy_goal matches several files in path`.

Fix action: Added short-name wrapper modules under `/home/yangfp/CAV/C/CAV/output/verify_20260605_010426v_array_sum_nonnegative/original/` for `int_array`, `uint_array`, `undef_uint_array`, and `array_shape` strategy goal/proof pairs, each re-exporting the `SimpleC.EE.QCP_demos_LLM` version.

Key fragment:

```coq
From SimpleC.EE.QCP_demos_LLM Require Export int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
Include SimpleC.EE.QCP_demos_LLM.int_array_strategy_proof.
```

Why this fixed it: The generated files remained unchanged, while `-Q "$ORIG" ""` resolved each short name to a unique wrapper module before Coq searched the shared `examples/` tree.

## Issue 3

Phenomenon: Several first-pass proof scripts failed due to local script shape problems rather than bad VCs: incorrect explicit use of `sublist_self`, specialization against an auto-named wrong hypothesis, and return-witness rewrites copied from another case.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_010426v_array_sum_nonnegative/coq/generated/array_sum_nonnegative_proof_manual.v`, helper `array_sum_nonnegative_spec_prefix_le`, witness `proof_of_array_sum_nonnegative_entail_wit_2_1`, and witness `proof_of_array_sum_nonnegative_return_wit_1`.

Fix action: Replaced brittle rewrites with robust shape-driven scripts:
- `replace l with (sublist 0 (Zlength l) l) at 2` before `sublist_split`
- explicitly named `Hrange` before specializing the prefix-bound lemma
- split `entail_wit_2_1` into the arithmetic side condition and the semantic equality
- used `match goal` to pick the current `sum = ...` and `Zlength l = n_pre` hypotheses in the return witness

Key fragment:

```coq
match goal with
| Hlen : Zlength l = n_pre |- _ => rewrite <- Hlen
end.
rewrite sublist_self by reflexivity.
```

Why this fixed it: The proof obligations were already the right ones; the failures came from brittle dependence on rewrite order and hypothesis numbering after `entailer!`. Matching by term shape made the scripts compile stably.

Final Result: Success

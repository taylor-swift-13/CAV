2026-06-05T00:00:00+08:00
Gate: symexec / generated VC review.
Phenomenon: The first invariant version used a single list `l` for both the current heap and the logical postcondition, so `array_fill_value_return_wit_1` lacked equalities connecting current parameters to `*_pre`, and `array_fill_value_entail_wit_2` asked for an impossible heap entailment from `IntArray.full ... (replace_Znth i k l)` to `IntArray.full ... l`.
Location: [annotated/verify_20260605_001513v_array_fill_value.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_001513v_array_fill_value.c), generated witnesses in [array_fill_value_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_001513v_array_fill_value/coq/generated/array_fill_value_goal.v).
Fix action: first preserved `a == a@pre`, `k == k@pre`, and `n == n@pre`, then replaced the invariant with `exists lr` so `l` stays the original array and `lr` tracks the mutable heap using a filled-prefix / untouched-suffix split.
Key fragment:
```c
/*@ Inv exists lr,
      ...
      (forall (j: Z), (0 <= j && j < i) => lr[j] == k) &&
      (forall (j: Z), (i <= j && j < n@pre) => lr[j] == l[j]) &&
      IntArray::full(a, n@pre, lr)
*/
```
Why it worked: after `a[i] = k`, the heap naturally becomes `replace_Znth i k lr`, and the next iteration can choose that updated list as the new existential witness.

2026-06-05T00:00:00+08:00
Gate: `coqc array_fill_value_proof_manual.v`.
Phenomenon: The first manual proof attempt failed because the proof script assumed the `entailer!` subgoals came in `(length, prefix, suffix)` order, but the actual order was `(suffix, prefix, length)`. A later replay also failed because `Zlength_replace_Znth`, `Znth_replace_Znth_same`, and `Znth_replace_Znth_diff` were not globally available in this environment.
Location: [array_fill_value_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_001513v_array_fill_value/coq/generated/array_fill_value_proof_manual.v).
Fix action: reordered the bullets to match the actual proof state, then added local helper lemmas for `replace_nth` / `replace_Znth` length and point-lookup behavior before proving `entail_wit_2` and `return_wit_1`.
Key Coq fragments:
```coq
Exists (replace_Znth i k_pre lr_2).
...
Lemma Znth_replace_Znth_diff : ...
```
Why it worked: the witnesses are pure list-update proofs, so local helper lemmas remove dependency on environment-specific exports and keep the proof deterministic.

2026-06-05T00:00:00+08:00
Gate: `coqc array_fill_value_goal.v` replay.
Phenomenon: generated short imports such as `Require Import int_array_strategy_goal.` matched both `QCP_demos_LLM` and `QCP_demos_human`, causing duplicate-path failure.
Location: [array_fill_value_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_001513v_array_fill_value/coq/generated/array_fill_value_goal.v:20).
Fix action: added local wrapper modules under [original/](/home/yangfp/CAV/C/CAV/output/verify_20260605_001513v_array_fill_value/original/) for `int_array`, `uint_array`, `undef_uint_array`, and `array_shape` goal/proof pairs, each re-exporting the `QCP_demos_LLM` module so `-Q "$ORIG" ""` resolves the short names uniquely during replay.
Why it worked: the generated Coq files stay unchanged while the load path now has a single unambiguous provider for each short strategy name.

2026-06-05T00:29:29+08:00
Result: `symexec` succeeded on the final annotated C, `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all compiled, `proof_manual.v` contains no `Admitted` / `admit` / `Abort` / new `Axiom`, and `coq/` cleanup removed non-`.v` files. Input/original C are unchanged; the annotated file differs only by verification annotations.
Final Result: Success

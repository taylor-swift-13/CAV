2026-06-05T00:00:00Z
Phenomenon: After the existential-list invariant rewrite, [array_fill_value_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_001513v_array_fill_value/coq/generated/array_fill_value_goal.v) contains exactly two manual obligations: `array_fill_value_entail_wit_2` for loop preservation after the store, and `array_fill_value_return_wit_1` for the loop-exit postcondition.
Location: generated theorems `array_fill_value_entail_wit_2` and `array_fill_value_return_wit_1`.
Repair action: Prove `entail_wit_2` by choosing `replace_Znth i k_pre lr_2` as the next loop witness, then split prefix and suffix index cases with `j = i` versus `j <> i`. Prove `return_wit_1` by choosing `lr_2` as the result list and deriving `i_2 = n_pre` from `i_2 >= n_pre` and `i_2 <= n_pre`.
Key Coq proof shape:
```coq
Exists (replace_Znth i k_pre lr_2).
...
destruct (Z.eq_dec j i).
```
and
```coq
assert (i_2 = n_pre) by lia; subst i_2.
Exists lr_2.
```
Why this change: The updated invariant already exposes the exact current heap list and the original suffix relation. The remaining work is pure list/arithmetic reasoning around a single replacement step and the equality forced by loop exit.

2026-06-05T00:00:00Z
Phenomenon: `coqc` then failed in [array_fill_value_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_001513v_array_fill_value/coq/generated/array_fill_value_proof_manual.v) because this environment does not provide `Znth_replace_Znth_diff` / `Znth_replace_Znth_same` / `Zlength_replace_Znth` as imported global lemmas, even though nearby verified workspaces use those names after defining them locally.
Location: manual proof compile at `proof_of_array_fill_value_entail_wit_2`, after bullet reordering matched the actual `entailer!` subgoal order.
Repair action: Add the standard local helper lemmas for `replace_nth` length, `nth_replace_nth_same`, `nth_replace_nth_diff`, `Zlength_replace_Znth`, `Znth_replace_Znth_same`, and `Znth_replace_Znth_diff`, using the same self-contained pattern as the allowed references `string_fill_char` and `array_init`.
Key Coq fragment:
```coq
Lemma Zlength_replace_Znth : ...
Lemma Znth_replace_Znth_same : ...
Lemma Znth_replace_Znth_diff : ...
```
Why this change: The witness proof is a pure list update proof. Making the replacement facts local to the generated manual file avoids dependence on environment-specific exports and keeps the replay deterministic.

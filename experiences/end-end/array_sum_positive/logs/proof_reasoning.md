## 2026-06-05 01:30:59 CST

Phenomenon: after regenerating VCs with the strengthened invariant, `proof_manual.v` still contains five manual lemmas: `proof_of_array_sum_positive_safety_wit_4`, `proof_of_array_sum_positive_entail_wit_1`, `proof_of_array_sum_positive_entail_wit_2_1`, `proof_of_array_sum_positive_entail_wit_2_2`, and `proof_of_array_sum_positive_return_wit_1`.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_012416v_array_sum_positive/coq/generated/array_sum_positive_goal.v` and `/home/yangfp/CAV/C/CAV/output/verify_20260605_012416v_array_sum_positive/coq/generated/array_sum_positive_proof_manual.v`.

Repair action: move to manual proof mode, but first establish a stable replay compile environment for the generated modules. The first replay attempt stopped at `array_sum_positive_goal.v` with:

```text
Error: Required library int_array_strategy_goal matches several files in path
```

Why this change: until the generated `goal.v` can be compiled deterministically, interactive proof inspection is unreliable. The fix is to provide workspace-local short-name wrappers for the conflicting strategy modules, so later proof iterations can target the actual lemma bodies instead of fighting load-path ambiguity.

## 2026-06-05 01:40:00 CST

Phenomenon: once the load path was stabilized, the remaining failures were concentrated in pure list/arithmetic witnesses:

- `proof_of_array_sum_positive_safety_wit_4`
- `proof_of_array_sum_positive_entail_wit_2_1`
- `proof_of_array_sum_positive_entail_wit_2_2`
- `proof_of_array_sum_positive_return_wit_1`

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_012416v_array_sum_positive/coq/generated/array_sum_positive_proof_manual.v`.

Repair action: add four local helper lemmas in `proof_manual.v`:

- `array_sum_positive_spec_nonneg`
- `array_sum_positive_spec_app`
- `array_sum_positive_spec_sublist_succ`
- `array_sum_positive_spec_prefix_le`

Then use short witness proofs:

```coq
pre_process.
entailer!.
rewrite H4.
rewrite array_sum_positive_spec_sublist_succ; try lia.
destruct (Z_gt_dec (Znth i l 0) 0); lia.
```

For the return witness, prove `i = n_pre` from `i >= n_pre` and `i <= n_pre`, rewrite `sublist 0 i l` to the full list using `sublist_self`, then close with `entailer!`.

Why this change: the remaining obligations were not missing program state anymore; they were exact facts about how the recursive spec behaves on an extended prefix and about monotonicity of the prefix sum inside the full list. Encoding those as local lemmas keeps the main witness proofs short and stable.

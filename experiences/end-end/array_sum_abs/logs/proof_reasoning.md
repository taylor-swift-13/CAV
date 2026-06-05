2026-06-05T00:00:00+08:00

Symptom: after the repaired `symexec`, [array_sum_abs_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/coq/generated/array_sum_abs_proof_manual.v:24) contained seven `Admitted` obligations: `safety_wit_4`, `safety_wit_5`, `safety_wit_6`, `entail_wit_1`, `entail_wit_2_1`, `entail_wit_2_2`, and `return_wit_1`.

Location: the corresponding VC statements in [array_sum_abs_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_005812v_array_sum_abs/coq/generated/array_sum_abs_goal.v:84) show three proof patterns:

1. arithmetic safety from the contract lower bound and total `sum_abs` bound;
2. one-step loop preservation, where `sum_abs(sublist 0 (i + 1) l)` must be related to `sum_abs(sublist 0 i l)` plus the newly processed element;
3. loop exit, where `i >= n_pre` and `i <= n_pre` must collapse the prefix `sublist(0, i, l)` to the full list.

Fix action: add helper lemmas inside `proof_manual.v` instead of hard-coding rewrites in every witness.

Key Coq bridge:

```coq
Lemma sum_abs_app : forall l1 l2,
  sum_abs (l1 ++ l2) = sum_abs l1 + sum_abs l2.

Lemma sum_abs_prefix_le : forall l i,
  0 <= i <= Zlength l ->
  sum_abs (sublist 0 i l) <= sum_abs l.

Lemma sum_abs_sublist_succ_nonneg ...
Lemma sum_abs_sublist_succ_neg ...
```

Why this change: the generated VCs are all instances of the same list decomposition fact. `sublist_split` plus `sublist_single` isolates the next array element as a one-element suffix, `sum_abs_app` turns that split into arithmetic, and `Z.abs_eq` / `Z.abs_neq` selects the correct branch-specific contribution. Once those helpers exist, the safety witnesses and entailment witnesses should be stable one-liners with `pre_process; entailer!;` followed by one rewrite and `lia`.

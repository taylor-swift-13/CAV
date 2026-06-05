# Proof Reasoning

## Iteration 1: reuse the standard prefix-count proof pattern after successful symexec

Fresh symexec on the current annotated file succeeded and generated the manual obligations in [array_count_negative_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_233715v_array_count_negative/coq/generated/array_count_negative_proof_manual.v:23). The file contains five admitted lemmas:

```coq
Lemma proof_of_array_count_negative_safety_wit_4 : array_count_negative_safety_wit_4.
Lemma proof_of_array_count_negative_entail_wit_1 : array_count_negative_entail_wit_1.
Lemma proof_of_array_count_negative_entail_wit_2_1 : array_count_negative_entail_wit_2_1.
Lemma proof_of_array_count_negative_entail_wit_2_2 : array_count_negative_entail_wit_2_2.
Lemma proof_of_array_count_negative_entail_wit_3 : array_count_negative_entail_wit_3.
```

Localization from `array_count_negative_goal.v`:

- `safety_wit_4` must show `count + 1` stays in signed-int range when `Znth i l 0 < 0`.
- `entail_wit_1` is the empty-prefix initialization fact `0 = array_count_negative_spec (sublist 0 0 l)`.
- `entail_wit_2_1` and `entail_wit_2_2` are the true/false branch preservation facts for extending `sublist 0 i l` to `sublist 0 (i + 1) l`.
- `entail_wit_3` is the loop-exit normalization from `sublist 0 i l` to the whole list once `i >= n_pre` and `i <= n_pre`.

Fix action: replace the admitted proofs with the same structure used by the completed `count_positive` and `array_count_zero` workspaces:

```coq
Lemma array_count_negative_spec_app_single :
  forall (l : list Z) (x : Z),
    array_count_negative_spec (l ++ x :: nil) =
    array_count_negative_spec l + (if Z_lt_dec x 0 then 1 else 0).

Lemma array_count_negative_spec_bounds :
  forall (l : list Z),
    0 <= array_count_negative_spec l <= Zlength l.
```

Then:

- `safety_wit_4`: instantiate the bounds lemma on `sublist 0 i l`, rewrite `Zlength_sublist`, and combine `count <= i`, `i < n_pre`, and the local `int` range for `n_pre` from `store_int_range`.
- `entail_wit_2_1` / `entail_wit_2_2`: rewrite `sublist 0 (i + 1) l` as `sublist 0 i l ++ [Znth i l 0]`, rewrite by `array_count_negative_spec_app_single`, and discharge the impossible branch of `Z_lt_dec` with the current branch hypothesis.
- `entail_wit_3`: derive `i = n_pre` by arithmetic, rewrite `sublist 0 n_pre l` to `l` using `Zlength l = n_pre`, and conclude by reflexivity.

Why this edit is appropriate: the generated VC is purely about list-prefix semantics and accumulator bounds; the array ownership is already stable and does not need more annotation changes. This is a proof-side repair, not a contract or symexec-shape problem.

## Iteration 2: replay compile hit duplicate short-name strategy imports before manual proof checking

Phenomenon: the first replay compile stopped before reaching the new proofs:

```text
File ".../array_count_negative_goal.v", line 21, characters 0-39:
Error: Required library int_array_strategy_goal matches several files in path
```

Localization: `array_count_negative_goal.v` imports short names such as `Require Import int_array_strategy_goal.` while the repository exposes both `SeparationLogic/examples/QCP_demos_LLM/int_array_strategy_goal.vo` and `.../QCP_demos_human/int_array_strategy_goal.vo`.

Fix action: add workspace-local wrapper modules under `/home/yangfp/CAV/C/CAV/output/verify_20260604_233715v_array_count_negative/coq/deps/` for all four strategy families (`int_array`, `uint_array`, `undef_uint_array`, `array_shape`) and their `goal/proof` modules, each re-exporting the `QCP_demos_LLM` version. The subsequent compile command will place `-Q "$DEPS" ""` before the shared `examples` tree so these short names resolve uniquely to the workspace wrappers.

Why this fixes the issue: it preserves generated `goal/proof_auto/proof_manual/goal_check` files unchanged, avoids touching the shared examples tree, and gives replay a deterministic short-name resolution path for the exact strategy modules used by symexec.

## Iteration 3: re-run symexec after restoring source-integrity and re-prove the refreshed exit witness

Phenomenon: after restoring the annotated C to the original executable loop form, the verify workflow required a fresh `symexec`. The regenerated manual file reverted to admitted placeholders and changed the loop-exit obligation set:

```coq
Lemma proof_of_array_count_negative_return_wit_1 : array_count_negative_return_wit_1.
Proof. Admitted.
```

while the previous `proof_of_array_count_negative_entail_wit_3` disappeared because the explicit post-loop `Assert` was removed from the annotated C.

Localization: `/home/yangfp/CAV/C/CAV/output/verify_20260604_233715v_array_count_negative/coq/generated/array_count_negative_proof_manual.v`.

Fix action: reapply the prefix-count helper lemmas and keep the same proofs for `safety_wit_4`, `entail_wit_1`, `entail_wit_2_1`, and `entail_wit_2_2`. Replace the old exit-normalization proof with a direct `return_wit_1` proof using `entailer!`, because the refreshed return witness already exposes `count = array_count_negative_spec l` in its antecedent.

Why this is the correct proof repair: the regenerated VC confirms that the invariant still carries the full semantic fact to function exit; only the witness naming and staging changed when the explicit exit assertion was removed to preserve source integrity. This is a proof-file refresh, not a new annotation weakness.

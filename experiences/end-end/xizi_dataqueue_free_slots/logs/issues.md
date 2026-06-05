2026-06-03

Issue: `proof_manual.v` initially contained unresolved `Admitted` placeholders for `proof_of_xizi_dataqueue_free_slots_safety_wit_4` and `proof_of_xizi_dataqueue_free_slots_return_wit_1`.

Location: `output/verify_20260603_000130v_xizi_dataqueue_free_slots/coq/generated/xizi_dataqueue_free_slots_proof_manual.v`.

Fix action: replaced the placeholders with explicit manual proofs plus helper lemmas for the free-slot arithmetic range, signed-int bounds, and the two case splits from the postcondition.

Key proof fragments:
- `free_slots_range` uses `Z.rem_bound_pos` to bound `((rear_pre - front_pre + max_len_pre) % ( max_len_pre ))`.
- `free_slots_case_front_le_rear` rewrites `Z.rem` to `mod` with `Z.rem_mod_nonneg`, then uses `Z.mod_add` and `Z.mod_small`.
- `free_slots_case_rear_lt_front` rewrites `Z.rem` to `mod` with `Z.rem_mod_nonneg`, then uses `Z.mod_small`.

Why this fix: the generated `%` operator is `Z.rem`, not Coq `mod`, so the helper lemmas had to match the generated VC exactly for the witness proofs to unify.

Result: `coqc` passed for `xizi_dataqueue_free_slots_goal.v`, `xizi_dataqueue_free_slots_proof_auto.v`, `xizi_dataqueue_free_slots_proof_manual.v`, and `xizi_dataqueue_free_slots_goal_check.v`. Cleanup removed all non-`.v` files from `coq/`, and `input/` has no extra intermediates.

Final Result: Success

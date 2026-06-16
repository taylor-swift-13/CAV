# Issues Log for p102_choose_num

## Issue 1: `Z.rem` vs `Z.modulo`
- **Location**: Return witness proofs (wit_1, wit_2, wit_3, wit_4)
- **Symptom**: Attempts to use `Z.mod_pos_bound` and `Zmod_even` on hypotheses of form `y_pre % 2 = 1` failed because `%` in QCP goals maps to `Z.rem`, not `Z.modulo`.
- **Root cause**: SimpleC's C-to-Coq translation uses `Z.rem` for the `%` operator (found in `SeparationLogic/IntLib.v`).
- **Fix**: Added helper lemmas that first convert `Z.rem a 2` to `Z.modulo a 2` using `Z.rem_mod_nonneg` (valid since inputs are positive), then apply standard `Z.modulo` lemmas.

## Issue 2: Setoid rewrite failure on `Z.even_sub`
- **Location**: Return wit_3 proof
- **Symptom**: `rewrite Z.even_sub` failed with "setoid rewrite failed: UNDEFINED EVARS".
- **Root cause**: The `sac` scope or imported modules enable generalized rewriting, which conflicts with plain equality lemmas for boolean-valued functions.
- **Fix**: Avoided `Z.even_sub` entirely. Instead proved `Z.even (a - 1) = true` from `Z.rem a 2 = 1` using `Z.even_pred` and `Z.negb_even`, which rewrote correctly.

## Issue 3: Proof structure discovery
- **Location**: Initial proof planning
- **Symptom**: Uncertainty about whether safety witnesses need proofs in `proof_manual.v`.
- **Fix**: All 16 safety witnesses were auto-generated in `proof_auto.v` with `Admitted`; the CAV workflow only requires `proof_manual.v` to have no `Admitted`. The 5 return witnesses were proved in `proof_manual.v`.

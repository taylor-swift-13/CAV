## 2026-06-04 - Issues log

### Issue 1: `lia` does not solve goal 4

**Phenomenon:** After `pre_process; entailer!; try lia`, one goal remained:
`year_pre % 4 <> 0 -> 1 = 0` with `H: year_pre % 400 = 0` in context.

**Localization:** `leap_year_proof_manual.v`, theorem `proof_of_leap_year_return_wit_4`.

**Root cause:** Goal 4 requires proving that `400 | year_pre → 4 | year_pre`. `lia` cannot deduce divisibility transitivity (4 | 400 | year_pre → 4 | year_pre) from modular arithmetic hypotheses alone.

**Fix:** Used explicit `Z.quot_rem` + `Z.rem_mul` to construct the proof manually.

---

### Issue 2: `%` is `Z.rem`, not `Z.modulo`

**Phenomenon:** `apply (proj2 (Z.mod_divide year_pre 4 ltac:(lia)))` failed with:
`Unable to unify "year_pre mod 4 = 0" with "year_pre % 4 = 0"`.

**Localization:** `leap_year_proof_manual.v`, goal after `apply H4`.

**Root cause:** In QCP's sac/assertion scope, `%` is `Z.rem` (C-style truncating remainder). `Z.mod_divide` uses `Z.modulo` (`mod`), which is Euclidean remainder. These differ syntactically in Coq even though they coincide for positive inputs.

**Fix:** Used `Z.quot_rem` (which uses `÷` = `Z.quot` and `%` = `Z.rem`) and `Z.rem_mul` instead of `Z.mod_divide` and `Z.mod_mul`.

**Why:** QCP translates C's `%` to `Z.rem`, not `Z.modulo`. Any future proof involving C modular arithmetic must use the `Z.rem`/`Z.quot` family of lemmas.

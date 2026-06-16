# Issues Log — p122_add_elements

## Issue 1: sac scope overrides `&&` and `=` for bool lemmas

**Symptom**: Placing helper lemmas after `Local Open Scope sac.` caused compile errors like "term has type bool while expected model -> Prop".

**Location**: `proof_manual.v` — helper lemma `two_digit_bool_equiv`

**Root cause**: `sac` scope redefines `&&` and `=` for `model -> Prop`, so `Z.leb A B && Z.leb C D` inside `sac` scope is parsed as sac conjunction, not bool.

**Fix**: Moved all helper lemmas (`two_digit_bool_equiv`, `sum_two_digit_upto_step`, `sum_two_digit_upto_nat_eq_fold_leb`, `sum_two_digit_upto_nat_eq_fold`, `sum_two_digit_upto_eq_fold`) before `Local Open Scope sac.`.

---

## Issue 2: `filter_ext` rewriting under binder

**Symptom**: `rewrite <- two_digit_bool_equiv` fails with "Found no subterm matching is_at_most_two_digits" when trying to rewrite inside `filter (fun x => ...)`.

**Root cause**: `is_at_most_two_digits` appears as a function argument to `filter`, not applied to a specific term, so rewrite cannot find a subterm to replace.

**Fix**: Proved `sum_two_digit_upto_nat_eq_fold_leb` using `Z.leb` form throughout, then proved `sum_two_digit_upto_nat_eq_fold` using `filter_ext + two_digit_bool_equiv`.

---

## Issue 3: `sets` scope makes `[x]` a singleton set

**Symptom**: `[nth n l 0]` has type "Z -> Prop" not "list Z" — `SetsClass.SetsClass` opens `sets` scope which makes `[x]` a singleton set notation.

**Fix**: Changed to `(nth n l 0 :: nil)` throughout `sum_two_digit_upto_nat_eq_fold_leb`.

---

## Issue 4: `firstn_all2` takes Z index not nat

**Symptom**: `apply firstn_all2; lia` fails with "The term 'S n' has type nat while expected Z".

**Root cause**: `AUXLib.ListLib`'s `firstn_all2` takes a Z index, not nat.

**Fix**: Replaced the `firstn_all2`-based proof with direct induction on `l`.

---

## Issue 5: `match goal` with concrete variable names fails

**Symptom**: `match goal with | Hrange : sum_two_digit_int_range k_pre lv |- _` fails with "reference not found: k_pre" even though `k_pre` is in scope after `pre_process`.

**Root cause**: Ltac `match goal` type patterns require Ltac metavariables (`?name`) for unification; bare names like `k_pre` are treated as Ltac references that must already be bound.

**Fix**: Changed all concrete variable references in match patterns to `?`-metavariables (`?kp`, `?lv2`, `?ii`, `?ss`).

---

## Issue 6: `entailer!` in `entail_wit_1` generates no subgoals

**Symptom**: `pre_process; entailer!.` followed by more tactics gives "No such goal".

**Root cause**: `entail_wit_1` (initialization) is trivially closed by `pre_process.` alone.

**Fix**: Changed proof to just `pre_process.`.

---

## Issue 7: `linarith` not found in sac scope

**Symptom**: Line containing `linarith` gives "The reference linarith was not found in the current environment".

**Root cause**: `linarith` from `Coq.micromega.Psatz` is not available in this project's Coq configuration, or conflicts with sac scope.

**Fix**: Replaced all `linarith` with `lia`.

---

## Issue 8: sac scope overrides `&&` in assert inside proof

**Symptom**: `assert (Hc: Z.leb (-99) (Znth i lv 0) && Z.leb (Znth i lv 0) 99 = true)` fails with "term has type bool while expected model -> Prop" inside proofs after `Local Open Scope sac.`.

**Root cause**: `&&` inside assert in sac scope is parsed as sac conjunction, expecting `model -> Prop` operands.

**Fix**: Asserted each `Z.leb` condition separately as `Z.leb X = true` / `Z.leb X = false` using `apply Z.leb_le` and `rewrite <- Bool.not_true_iff_false; rewrite Z.leb_le`. For `entail_wit_2_3` used `rewrite Hle, Bool.andb_false_r`.

---

## Issue 9: `sum_two_digit_upto_eq_fold` rewrite direction for `return_wit_1`

**Note**: For `return_wit_1`, the goal after `unfold problem_122_spec` was `s = fold_left ... (sublist 0 k_pre lv) 0`. Used `rewrite <- sum_two_digit_upto_eq_fold by lia` (right-to-left) to replace the fold with `sum_two_digit_upto k_pre lv`, then `assumption` closed with hypothesis `s = sum_two_digit_upto k_pre lv`.

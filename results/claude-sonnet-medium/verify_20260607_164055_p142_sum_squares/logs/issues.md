# Issues Encountered: p142_sum_squares Verification

## Issue 1: `ring` failure in helper lemma `transformed_sum_from_app`

**Location:** `proof_manual.v`, lemma `transformed_sum_from_app`

**Symptom:** `ring` tactic could not close goals where arguments differed syntactically
(`start` vs `start + 0`; `start + 1 + Zlength xs` vs `start + (Zlength xs + 1)`).

**Fix:** Added `replace ... with ... by lia` before each `ring` call to normalize arithmetic.

---

## Issue 2: `=?` notation conflict in `Local Open Scope sac`

**Location:** All uses of `Z.rem i k =? 0` in `proof_manual.v`

**Symptom:** In `Local Open Scope sac.`, the `=?` notation is overloaded for string
comparison. Writing `Z.rem i 3 =? 0` triggers a type error expecting `string` on the left.

**Fix:** Replaced all `Z.rem i k =? 0` with explicit `Z.eqb (Z.rem i k) 0`, using
`assert (Htrue : Z.eqb (Z.rem i k) 0 = true) by (apply Z.eqb_eq; exact H)` pattern.

---

## Issue 3: `lia` / `dump_pre_spatial` failures with `%`-hypothesis in context

**Location:** `safety_wit_6/7/11/12/13/17`, `entail_wit_2_1/2_2/2_3`

**Symptom:** When `H: Z.rem i 3 = 0` (displayed as `H: i%3=0` in sac scope) is in
context, `lia` fails due to the `%` notation conflict with string operations.

**Fix:** `clear H [H0]` before calling `lia`. In bullets that use `ring` (not `lia`),
no clearing is needed — `ring` handles arithmetic without parsing the `%` notation.

---

## Issue 4: `entail_wit_1` over-specified

**Location:** `proof_manual.v`, `entail_wit_1`

**Symptom:** Attempting `split_pure_spatial` / `split_pures` after `pre_process` gave
"No such goal" because `pre_process` closes the lemma entirely.

**Fix:** Reduced proof to `pre_process. Qed.`

---

## Issue 5: Use-after-clear of `%`-hypothesis in `entail_wit_2_x` last bullet

**Location:** `proof_manual.v`, lines 213, 239, 266 (last `split_pures` bullet
in each of `entail_wit_2_1`, `entail_wit_2_2`, `entail_wit_2_3`)

**Symptom:** After `clear H [H0]` before `dump_pre_spatial`, subsequent `exact H`
(or `exact H0`) inside `{ unfold transformed_value. ... }` failed with:
```
The term "H" has type "forall A : Type, (A -> A) -> A -> A"
while it is expected to have type "i % 3 = 0".
```
Coq resolved `H` to a global identifier instead of a local hypothesis.

**Fix:** Removed the `clear H [H0]` from the last bullet only. Since the last
bullet uses `ring` (not `lia`), the `%`-hypothesis does not cause failures, and
`H` / `H0` remain available for `exact H` / `exact H0`.

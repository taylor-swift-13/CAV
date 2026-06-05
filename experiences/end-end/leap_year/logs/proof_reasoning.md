## 2026-06-04 - Proof analysis for leap_year_return_wit_4

### VC structure

Goal: `leap_year_return_wit_4`

```
forall (year_pre: Z),
  " (year_pre % 400 = 0) "  &&  " (1 <= year_pre) "  &&  emp
|--
  " (year_pre % 400 = 0 -> 1 = 1) "
  &&  " ((year_pre % 100 = 0 /\ year_pre % 400 <> 0) -> 1 = 0) "
  &&  " ((year_pre % 4 = 0 /\ year_pre % 100 <> 0) -> 1 = 1) "
  &&  " (year_pre % 4 <> 0 -> 1 = 0) "
  &&  emp
```

Preconditions: `year_pre % 400 = 0`, `1 <= year_pre`.

Four implications to prove:
1. `year_pre % 400 = 0 -> 1 = 1` — trivially true (1=1 always)
2. `(year_pre % 100 = 0 /\ year_pre % 400 <> 0) -> 1 = 0` — vacuously true: premise's second conjunct contradicts precondition `year_pre % 400 = 0`
3. `(year_pre % 4 = 0 /\ year_pre % 100 <> 0) -> 1 = 1` — trivially true (1=1 always)
4. `year_pre % 4 <> 0 -> 1 = 0` — vacuously true: premise contradicts fact that `400 | year_pre -> 4 | year_pre`

Goals 1–3 should be discharged by `lia`. Goal 4 requires showing `year_pre % 4 = 0` from `year_pre % 400 = 0` (divisibility transitivity: 4 | 400 | year_pre → 4 | year_pre).

### Round 1: try simplest template

Template from README §3: `Proof. pre_process; entailer!; try lia. Qed.`

**Result: FAIL** — `Attempt to save an incomplete proof (there are remaining open goals)`.

After `pre_process; entailer!`, goals 1–3 were solved automatically. Only goal 4 remained:
```
year_pre : Z
H : year_pre % 400 = 0
H0 : 1 <= year_pre
============================
year_pre % 4 <> 0 -> 1 = 0
```

`try lia` did not close this goal because `lia` cannot derive `year_pre % 4 = 0` from `year_pre % 400 = 0` — divisibility transitivity is outside `lia`'s scope here.

### Round 2: explicit proof with Z.mod_divide

Tried using `Z.mod_divide year_pre 4` to convert goal to `(4 | year_pre)`.

**Result: FAIL** — `Unable to unify "year_pre mod 4 = 0" with "year_pre % 4 = 0"`.

Key insight: in QCP's sac scope, `%` is `Z.rem` (truncating remainder), while `Z.mod_divide` talks about `Z.modulo` (`mod`). These are different Coq terms even though they coincide for positive inputs.

### Round 3: use Z.rem lemmas

`%` = `Z.rem`, so we need:
- `Z.quot_rem : forall a b : Z, b <> 0 -> a = b * (a ÷ b) + a % b`
- `Z.rem_mul : forall a b : Z, b <> 0 -> (a * b) % b = 0`

Proof:
1. `pose proof (Z.quot_rem year_pre 400 ltac:(lia)) as Hqr` gives `year_pre = 400 * (year_pre ÷ 400) + year_pre % 400`
2. With `H: year_pre % 400 = 0`, `lia` derives `year_pre = 100 * (year_pre ÷ 400) * 4` (since `400 = 100 * 4`)
3. `rewrite Heq` + `apply Z.rem_mul` closes the goal: `(100 * (year_pre ÷ 400) * 4) % 4 = 0`

**Result: SUCCESS** — `proof_manual.v` and `goal_check.v` both compiled cleanly.

Final proof:
```coq
Lemma proof_of_leap_year_return_wit_4 : leap_year_return_wit_4.
Proof.
  pre_process; entailer!.
  intro H4.
  exfalso.
  apply H4.
  pose proof (Z.quot_rem year_pre 400 ltac:(lia)) as Hqr.
  assert (Heq : year_pre = 100 * (year_pre ÷ 400) * 4) by lia.
  rewrite Heq.
  apply Z.rem_mul. lia.
Qed.
```

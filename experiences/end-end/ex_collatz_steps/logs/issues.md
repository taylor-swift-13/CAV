# Issues Log

## Iteration 1: missing loop invariant blocked symbolic execution

- Phenomenon: the first `symexec` run on `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_073258v_ex_collatz_steps.c` failed with `Error: Lack of assertions in some paths for the loop!`.
- Location: the only loop `while (x != 1)` in target function `ex_collatz_steps`.
- Repair action: added a loop invariant preserving `0 <= steps <= fuel`, `n == n@pre`, `ex_collatz_safe_fuel(x, fuel - steps)`, and the semantic decomposition `steps + ex_collatz_steps_fuel(x, fuel - steps) == ex_collatz_steps_fuel(n@pre, fuel)`.
- Key snippet:
```c
/*@ Inv
      n == n@pre &&
      0 <= steps &&
      steps <= fuel &&
      ex_collatz_safe_fuel(x, fuel - steps) &&
      steps + ex_collatz_steps_fuel(x, fuel - steps) == ex_collatz_steps_fuel(n@pre, fuel)
*/
```
- Why this fixed it: the loop body executes exactly one Collatz transition and consumes exactly one fuel unit, so the invariant had to expose the remaining-fuel recurrence rather than only raw bounds.

## Iteration 2: proof helpers needed the C `%` operator semantics, not `Z.mod`

- Phenomenon: the first manual-proof attempt failed in `ex_collatz_steps_proof_manual.v` when applying odd/even helper lemmas, because the generated witnesses use `%` from C semantics (`Z.rem`) while the initial helper lemmas were written against `Z.mod`.
- Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_073258v_ex_collatz_steps/coq/generated/ex_collatz_steps_proof_manual.v`, helper lemmas bridging parity to `Z.even`.
- Repair action: replaced the parity bridge helpers with `Z.rem`-based lemmas:
```coq
Lemma rem2_zero_even_true : forall x, Z.rem x 2 = 0 -> Z.even x = true.
Lemma rem2_nonzero_even_false : forall x, Z.rem x 2 <> 0 -> Z.even x = false.
```
- Why this fixed it: the generated Collatz branch witnesses come from the C expression `x % 2`, so the proof has to consume `Z.rem` facts directly before relating them to the Coq-side `Z.even` recursion.

## Iteration 3: increment and branch-preservation witnesses needed explicit “remaining fuel is positive”

- Phenomenon: `coqc` failed on the safety witnesses for `steps++` and on the branch-preservation witnesses because `lia` alone could not justify `steps + 1 <= fuel` or `steps + 1 <= INT_MAX`.
- Location: proof obligations `proof_of_ex_collatz_steps_safety_wit_12`, `proof_of_ex_collatz_steps_safety_wit_13`, `proof_of_ex_collatz_steps_entail_wit_2_1`, and `proof_of_ex_collatz_steps_entail_wit_2_2`.
- Repair action: introduced and used the helper:
```coq
Lemma ex_collatz_safe_fuel_nonterminal_positive :
  forall n fuel, 0 <= fuel -> n <> 1 -> ex_collatz_safe_fuel n fuel -> 0 < fuel.
```
  Then each affected witness first derives `0 < fuel - steps` from `x <> 1` and `ex_collatz_safe_fuel x (fuel - steps)`, and only afterwards proves the `steps + 1` bounds.
- Why this fixed it: the annotation invariant records only `steps <= fuel`; the strict inequality required for the next iteration comes from the semantic meaning of a nonterminal Collatz state, not from arithmetic alone.

## Iteration 4: initial-state and branch-step semantic witnesses needed explicit normalization

- Phenomenon: `proof_of_ex_collatz_steps_entail_wit_1` and the two branch entailment witnesses did not close under a raw `entailer!; lia` proof because their goals still contained unreduced `fuel - 0`, `fuel - steps = rem + 1`, and one-step recurrence shapes.
- Location: `ex_collatz_steps_goal.v` witnesses `ex_collatz_steps_entail_wit_1`, `ex_collatz_steps_entail_wit_2_1`, `ex_collatz_steps_entail_wit_2_2`.
- Repair action:
  - normalized `fuel - 0` to `fuel` explicitly in the initialization witness,
  - added `ex_collatz_steps_fuel_unfold` and `ex_collatz_safe_fuel_unfold`,
  - proved even/odd one-step helper lemmas and rewrote `x ÷ 2` to `x / 2` using `Z.quot_div_nonneg`.
- Key proof fragment:
```coq
assert (Heq : fuel - steps = (fuel - (steps + 1)) + 1) by lia.
rewrite Heq in H3.
pose proof (ex_collatz_even_safe_step x (fuel - (steps + 1)) Hrem H0 H H3) as [_ Hchild].
```
- Why this fixed it: the invariant was already the right semantic shape; the proof just needed the recursive definitions exposed one fuel step at a time.

## Final machine checks

- `symexec` on the latest annotated file succeeded and regenerated:
  - `ex_collatz_steps_goal.v`
  - `ex_collatz_steps_proof_auto.v`
  - `ex_collatz_steps_proof_manual.v`
  - `ex_collatz_steps_goal_check.v`
- `coqc` succeeded on:
  - `original/ex_collatz_steps.v`
  - `coq/generated/ex_collatz_steps_goal.v`
  - `coq/generated/ex_collatz_steps_proof_auto.v`
  - `coq/generated/ex_collatz_steps_proof_manual.v`
  - `coq/generated/ex_collatz_steps_goal_check.v`
- Source integrity check:
  - `input/ex_collatz_steps.c` matches `original/ex_collatz_steps.c`
  - `input/ex_collatz_steps.v` matches `original/ex_collatz_steps.v`
- `proof_manual.v` contains no `Admitted`, `admit`, `Abort`, or proof-bypassing axioms.

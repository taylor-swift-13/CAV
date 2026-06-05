# Proof Reasoning

## Iteration 1: discharge pure safety goals and prove one-step Collatz loop preservation

- Phenomenon: `symexec` succeeded, but `/home/yangfp/CAV/C/CAV/output/verify_20260605_073258v_ex_collatz_steps/coq/generated/ex_collatz_steps_proof_manual.v` contained only `Admitted` placeholders for 13 safety witnesses, two loop-preservation entailment witnesses, and the return witness.
- Location: generated proof file `.../coq/generated/ex_collatz_steps_proof_manual.v`; semantic witnesses are declared in `.../coq/generated/ex_collatz_steps_goal.v`, especially `ex_collatz_steps_entail_wit_2_1`, `ex_collatz_steps_entail_wit_2_2`, and `ex_collatz_steps_return_wit_1`.
- Repair action: add local helper lemmas in `proof_manual.v` for:
  - unfolding `ex_collatz_safe_fuel` and `ex_collatz_steps_fuel` on a successor fuel,
  - bridging `x % 2 == 0` / `x % 2 <> 0` to `Z.even x = true` / `false`,
  - extracting the safe next-state facts for the even and odd Collatz branches,
  - reducing `ex_collatz_steps_fuel 1 rem` to `0`.
- Key proof plan:

```coq
Lemma ex_collatz_steps_fuel_unfold :
  forall n fuel, 0 <= fuel ->
    ex_collatz_steps_fuel n (fuel + 1) =
    if Z.eqb n 1 then 0 else 1 + ex_collatz_steps_fuel (ex_collatz_next n) fuel.

Lemma ex_collatz_even_safe_step :
  forall x rem, ... ->
    1 <= x <= 9223372036854775807 /\ ex_collatz_safe_fuel (x / 2) rem.

Lemma ex_collatz_odd_safe_step :
  forall x rem, ... ->
    1 <= x <= 9223372036854775807 /\
    x <= 3074457345618258602 /\
    ex_collatz_safe_fuel (3 * x + 1) rem.
```

- Why this fix: the generated VCs are pure consequences of the annotation semantics and the companion `ex_collatz_steps.v` definitions. The loop invariant already matches the mathematical recurrence, so the remaining proof work is to expose one-step recursive unfoldings and arithmetic side conditions, not to change annotation shape again.

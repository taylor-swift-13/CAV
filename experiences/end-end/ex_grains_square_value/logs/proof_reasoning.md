## 2026-06-05 08:11:19 CST

Phenomenon: `symexec` succeeded, but [ex_grains_square_value_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_080500v_ex_grains_square_value/coq/generated/ex_grains_square_value_proof_manual.v:1) contains four manual obligations: `safety_wit_3`, `entail_wit_1`, `entail_wit_2`, and `return_wit_1`.

Location: generated witness definitions in [ex_grains_square_value_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_080500v_ex_grains_square_value/coq/generated/ex_grains_square_value_goal.v:47), especially the loop-step and loop-exit VCs.

Repair action: prove the witnesses with one local arithmetic helper lemma:

```coq
Lemma power_nonnegative_z_step :
  forall i : Z,
    1 <= i ->
    power_nonnegative_z 2 i = power_nonnegative_z 2 (i - 1) * 2.
```

Then:
- `entail_wit_1`: discharge by `pre_process; entailer!` plus computation of `power_nonnegative_z 2 0`.
- `entail_wit_2`: rewrite `value` with the invariant equation and use `power_nonnegative_z_step`.
- `return_wit_1`: combine `i >= square_pre` and `i <= square_pre` to get `i = square_pre`, then rewrite.
- `safety_wit_3`: instantiate the quantified contract bound at `k = i`, use `i < square_pre` to show `i <= square_pre - 1`, rewrite with the step lemma, and finish both bounds by `lia`.

Why this change: the generated VCs are purely scalar and already contain the full loop invariant facts. The only missing bridge is the closed-form recurrence from `2^(i-1)` to `2^i`; once that is explicit, the remaining proofs are direct arithmetic consequences of the contract and loop guard.

## 2026-06-05 08:11:19 CST

Phenomenon: first `coqc` replay failed at [ex_grains_square_value_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_080500v_ex_grains_square_value/coq/generated/ex_grains_square_value_proof_manual.v:59) with `Error: No such goal.`

Location: theorem `proof_of_ex_grains_square_value_entail_wit_1`.

Repair action: remove the trailing `vm_compute.` / `reflexivity.` after `pre_process; entailer!`.

Key error:

```text
File ".../ex_grains_square_value_proof_manual.v", line 59, characters 2-12:
Error: No such goal.
```

Why this change: for this witness the initialization facts are already first-order tautologies, so `entailer!` solves the theorem completely. Keeping any extra tactic after that leaves the proof script structurally invalid.

## 2026-06-05 08:11:19 CST

Phenomenon: after removing the tail tactics, `coqc` still failed at the same theorem because [ex_grains_square_value_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_080500v_ex_grains_square_value/coq/generated/ex_grains_square_value_proof_manual.v:59) still executed `entailer!` with no open goal.

Location: theorem `proof_of_ex_grains_square_value_entail_wit_1`.

Repair action: reduce the whole proof to just `pre_process.`.

Key observation from `coqtop`: `Goal ex_grains_square_value_entail_wit_1. pre_process.` immediately produced `No more goals.`

Why this change: this generated witness is a pure initialization entailment that the QCP pre-processing tactic already normalizes and solves completely; any follow-up tactic is guaranteed to fail structurally.

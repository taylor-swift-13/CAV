## Iteration 1

Phenomenon: `/home/yangfp/CAV/C/CAV/output/verify_20260605_075354v_ex_darts_score/coq/generated/ex_darts_score_proof_manual.v` contained exactly three manual obligations, `proof_of_ex_darts_score_safety_wit_1`, `proof_of_ex_darts_score_safety_wit_2`, and `proof_of_ex_darts_score_safety_wit_3`, all still `Admitted`.

Location: the corresponding VC definitions in `/home/yangfp/CAV/C/CAV/output/verify_20260605_075354v_ex_darts_score/coq/generated/ex_darts_score_goal.v` are pure arithmetic safety entailments:
- `safety_wit_1`: prove `INT_MIN <= x_pre * x_pre + y_pre * y_pre <= INT_MAX`
- `safety_wit_2`: prove `INT_MIN <= y_pre * y_pre <= INT_MAX`
- `safety_wit_3`: prove `INT_MIN <= x_pre * x_pre <= INT_MAX`

Fix action: replaced each `Admitted` with the standard straight-line arithmetic skeleton:

```coq
Proof.
  pre_process.
  entailer!.
  lia.
Qed.
```

Why this change: these witnesses do not require heap rearrangement or existential witnesses. `pre_process` exposes the pure bounds from the precondition, `entailer!` removes the unchanged spatial context, and `lia` should solve the remaining integer range goals directly from the generated assumptions.

## Iteration 2

Phenomenon: replay compilation failed at `/home/yangfp/CAV/C/CAV/output/verify_20260605_075354v_ex_darts_score/coq/generated/ex_darts_score_proof_manual.v:25` with `Error: No such goal.`

Location: the failure occurred in `proof_of_ex_darts_score_safety_wit_1` immediately after:

```coq
pre_process.
entailer!.
lia.
```

Fix action: changed the trailing arithmetic step in all three lemmas from `lia.` to `try lia.`.

Why this change: the error shows `entailer!` already discharges the witness in this generated VC shape, so an unconditional `lia` runs after the proof is finished. `try lia` preserves the same proof skeleton while remaining valid whether `entailer!` leaves a pure arithmetic side goal or closes the theorem outright.

## Iteration 3

Phenomenon: replay compilation still failed at the same location with the same `No such goal` error after switching to `try lia`.

Location: `proof_of_ex_darts_score_safety_wit_1` in `/home/yangfp/CAV/C/CAV/output/verify_20260605_075354v_ex_darts_score/coq/generated/ex_darts_score_proof_manual.v`, line 25.

Fix action: removed the trailing arithmetic tactic from all three lemmas, leaving:

```coq
Proof.
  pre_process.
  entailer!.
Qed.
```

Why this change: once `entailer!` solves the entailment, Coq accepts `Qed.` immediately. Even `try lia` still attempts to run a tactic after the theorem is complete, which reproduces `No such goal`. The minimal stable script for this VC shape is therefore just `pre_process; entailer!`.

## Iteration 4

Phenomenon: replay still failed with `No such goal`, and the numbered file confirmed the error position is exactly the `entailer!` line (`proof_manual.v:25`), not `Qed.`.

Location: `proof_of_ex_darts_score_safety_wit_1` in `/home/yangfp/CAV/C/CAV/output/verify_20260605_075354v_ex_darts_score/coq/generated/ex_darts_score_proof_manual.v`.

Fix action: removed `entailer!` from all three lemmas, leaving each proof as:

```coq
Proof.
  pre_process.
Qed.
```

Why this change: the only remaining explanation consistent with the stable line number is that `pre_process` itself fully discharges these trivial safety witnesses in the generated environment. In that case any subsequent tactic, including `entailer!`, necessarily fails with `No such goal`.

## Iteration 5

Phenomenon: full replay from `ex_darts_score_goal.v` through `ex_darts_score_goal_check.v` succeeded after reducing the three manual proofs to `pre_process.` only.

Location: successful compilation sequence run from `/home/yangfp/CAV/C/CAV/QualifiedCProgramming/SeparationLogic` against:
- `/home/yangfp/CAV/C/CAV/output/verify_20260605_075354v_ex_darts_score/coq/generated/ex_darts_score_goal.v`
- `/home/yangfp/CAV/C/CAV/output/verify_20260605_075354v_ex_darts_score/coq/generated/ex_darts_score_proof_auto.v`
- `/home/yangfp/CAV/C/CAV/output/verify_20260605_075354v_ex_darts_score/coq/generated/ex_darts_score_proof_manual.v`
- `/home/yangfp/CAV/C/CAV/output/verify_20260605_075354v_ex_darts_score/coq/generated/ex_darts_score_goal_check.v`

Fix action: none beyond the Iteration 4 proof simplification. Per verify cleanup rules, removed non-`.v` artifacts under `coq/` afterward.

Why this change: the generated safety witnesses were fully handled by `pre_process`, and the successful replay confirms there is no hidden arithmetic side-condition or contract gap in the current VC.

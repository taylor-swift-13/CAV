## Iteration 1

No blocking issue at this stage. The workspace started in proof-only mode with generated VCs already present; the first stable task was to replace the three remaining `Admitted` placeholders in `coq/generated/ex_darts_score_proof_manual.v` and then replay Coq compilation through `goal_check.v`.

## Iteration 2

First replay failure was non-blocking: `coqc` reported `No such goal` at `coq/generated/ex_darts_score_proof_manual.v:25` because `entailer!` had already closed `proof_of_ex_darts_score_safety_wit_1` before the explicit `lia.` step. Adjusted all three lemmas to end with `try lia.` and continued the compile loop.

## Iteration 3

Second replay failure confirmed the same root cause: `try lia.` still executes after `entailer!` has already completed the proof, so Coq again reported `No such goal`. Removed the trailing tactic entirely from the three manual lemmas and continued replay.

## Iteration 4

Third replay failure narrowed the root cause further: the stable error location stayed on `entailer!`, showing that `pre_process` had already closed the theorem. Reduced the three manual proofs to `pre_process.` only and continued replay.

## Iteration 5

Compilation replay succeeded through `coq/generated/ex_darts_score_goal_check.v`. No remaining blockers were found, and cleanup removed non-`.v` files under `coq/`.

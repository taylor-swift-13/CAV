From SimpleC.EE.CAV.ground_truth_p084_solve Require Import p084_solve_goal p084_solve_proof_auto p084_solve_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p084_solve_proof_auto.
  Include p084_solve_proof_manual.
End VC_Correctness.

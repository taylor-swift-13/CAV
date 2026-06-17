From SimpleC.EE.CAV.ground_truth_p161_solve Require Import p161_solve_goal p161_solve_proof_auto p161_solve_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p161_solve_proof_auto.
  Include p161_solve_proof_manual.
End VC_Correctness.

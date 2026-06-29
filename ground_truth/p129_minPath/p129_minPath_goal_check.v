From SimpleC.EE.CAV.ground_truth_p129_minPath Require Import p129_minPath_goal p129_minPath_proof_auto p129_minPath_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_ptr_array2_strategy_proof.
  Include int_array_strategy_proof.
  Include p129_minPath_proof_auto.
  Include p129_minPath_proof_manual.
End VC_Correctness.

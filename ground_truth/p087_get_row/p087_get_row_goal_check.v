From SimpleC.EE.CAV.ground_truth_p087_get_row Require Import p087_get_row_goal p087_get_row_proof_auto p087_get_row_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_ptr_array2_strategy_proof.
  Include int_array_strategy_proof.
  Include p087_get_row_proof_auto.
  Include p087_get_row_proof_manual.
End VC_Correctness.

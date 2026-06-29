From SimpleC.EE.CAV.ground_truth_p115_max_fill Require Import p115_max_fill_goal p115_max_fill_proof_auto p115_max_fill_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_ptr_array2_strategy_proof.
  Include int_array_strategy_proof.
  Include p115_max_fill_proof_auto.
  Include p115_max_fill_proof_manual.
End VC_Correctness.

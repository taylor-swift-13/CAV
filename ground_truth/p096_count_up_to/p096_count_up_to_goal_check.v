From SimpleC.EE.CAV.ground_truth_p096_count_up_to Require Import p096_count_up_to_goal p096_count_up_to_proof_auto p096_count_up_to_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p096_count_up_to_proof_auto.
  Include p096_count_up_to_proof_manual.
End VC_Correctness.

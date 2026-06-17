From SimpleC.EE.CAV.ground_truth_p052_below_threshold Require Import p052_below_threshold_goal p052_below_threshold_proof_auto p052_below_threshold_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p052_below_threshold_proof_auto.
  Include p052_below_threshold_proof_manual.
End VC_Correctness.

From SimpleC.EE.CAV.ground_truth_p152_compare Require Import p152_compare_goal p152_compare_proof_auto p152_compare_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p152_compare_proof_auto.
  Include p152_compare_proof_manual.
End VC_Correctness.

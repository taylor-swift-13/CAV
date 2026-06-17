From SimpleC.EE.CAV.ground_truth_p033_sort_third Require Import p033_sort_third_goal p033_sort_third_proof_auto p033_sort_third_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p033_sort_third_proof_auto.
  Include p033_sort_third_proof_manual.
End VC_Correctness.

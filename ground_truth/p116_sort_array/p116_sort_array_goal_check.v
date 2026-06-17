From SimpleC.EE.CAV.ground_truth_p116_sort_array Require Import p116_sort_array_goal p116_sort_array_proof_auto p116_sort_array_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p116_sort_array_proof_auto.
  Include p116_sort_array_proof_manual.
End VC_Correctness.

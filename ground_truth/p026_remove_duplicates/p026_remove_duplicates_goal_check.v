From SimpleC.EE.CAV.ground_truth_p026_remove_duplicates Require Import p026_remove_duplicates_goal p026_remove_duplicates_proof_auto p026_remove_duplicates_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p026_remove_duplicates_proof_auto.
  Include p026_remove_duplicates_proof_manual.
End VC_Correctness.

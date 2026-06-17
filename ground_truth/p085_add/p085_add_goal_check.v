From SimpleC.EE.CAV.ground_truth_p085_add Require Import p085_add_goal p085_add_proof_auto p085_add_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p085_add_proof_auto.
  Include p085_add_proof_manual.
End VC_Correctness.

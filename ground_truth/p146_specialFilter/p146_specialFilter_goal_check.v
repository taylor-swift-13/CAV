From SimpleC.EE.CAV.ground_truth_p146_specialFilter Require Import p146_specialFilter_goal p146_specialFilter_proof_auto p146_specialFilter_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p146_specialFilter_proof_auto.
  Include p146_specialFilter_proof_manual.
End VC_Correctness.

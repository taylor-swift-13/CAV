From SimpleC.EE.CAV.ground_truth_p068_pluck Require Import p068_pluck_goal p068_pluck_proof_auto p068_pluck_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p068_pluck_proof_auto.
  Include p068_pluck_proof_manual.
End VC_Correctness.

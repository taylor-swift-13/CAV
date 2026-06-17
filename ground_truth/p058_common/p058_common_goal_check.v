From SimpleC.EE.CAV.ground_truth_p058_common Require Import p058_common_goal p058_common_proof_auto p058_common_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p058_common_proof_auto.
  Include p058_common_proof_manual.
End VC_Correctness.

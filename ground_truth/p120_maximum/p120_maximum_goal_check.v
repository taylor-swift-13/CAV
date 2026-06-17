From SimpleC.EE.CAV.ground_truth_p120_maximum Require Import p120_maximum_goal p120_maximum_proof_auto p120_maximum_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p120_maximum_proof_auto.
  Include p120_maximum_proof_manual.
End VC_Correctness.

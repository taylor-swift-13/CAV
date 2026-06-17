From SimpleC.EE.CAV.ground_truth_p135_can_arrange Require Import p135_can_arrange_goal p135_can_arrange_proof_auto p135_can_arrange_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p135_can_arrange_proof_auto.
  Include p135_can_arrange_proof_manual.
End VC_Correctness.

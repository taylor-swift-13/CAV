From SimpleC.EE.CAV.ground_truth_p130_tri Require Import p130_tri_goal p130_tri_proof_auto p130_tri_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p130_tri_proof_auto.
  Include p130_tri_proof_manual.
End VC_Correctness.

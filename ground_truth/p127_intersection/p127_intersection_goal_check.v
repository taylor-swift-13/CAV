From SimpleC.EE.CAV.ground_truth_p127_intersection Require Import p127_intersection_goal p127_intersection_proof_auto p127_intersection_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p127_intersection_proof_auto.
  Include p127_intersection_proof_manual.
End VC_Correctness.

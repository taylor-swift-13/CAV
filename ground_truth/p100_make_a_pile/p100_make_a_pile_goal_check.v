From SimpleC.EE.CAV.ground_truth_p100_make_a_pile Require Import p100_make_a_pile_goal p100_make_a_pile_proof_auto p100_make_a_pile_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p100_make_a_pile_proof_auto.
  Include p100_make_a_pile_proof_manual.
End VC_Correctness.

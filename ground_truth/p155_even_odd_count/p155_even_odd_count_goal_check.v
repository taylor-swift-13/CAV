From SimpleC.EE.CAV.ground_truth_p155_even_odd_count Require Import p155_even_odd_count_goal p155_even_odd_count_proof_auto p155_even_odd_count_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p155_even_odd_count_proof_auto.
  Include p155_even_odd_count_proof_manual.
End VC_Correctness.

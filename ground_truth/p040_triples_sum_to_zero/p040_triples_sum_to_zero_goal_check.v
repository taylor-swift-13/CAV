From SimpleC.EE.CAV.ground_truth_p040_triples_sum_to_zero Require Import p040_triples_sum_to_zero_goal p040_triples_sum_to_zero_proof_auto p040_triples_sum_to_zero_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p040_triples_sum_to_zero_proof_auto.
  Include p040_triples_sum_to_zero_proof_manual.
End VC_Correctness.

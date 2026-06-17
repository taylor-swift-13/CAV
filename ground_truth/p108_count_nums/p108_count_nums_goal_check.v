From SimpleC.EE.CAV.ground_truth_p108_count_nums Require Import p108_count_nums_goal p108_count_nums_proof_auto p108_count_nums_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p108_count_nums_proof_auto.
  Include p108_count_nums_proof_manual.
End VC_Correctness.

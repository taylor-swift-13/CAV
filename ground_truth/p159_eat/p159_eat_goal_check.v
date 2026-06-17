From SimpleC.EE.CAV.ground_truth_p159_eat Require Import p159_eat_goal p159_eat_proof_auto p159_eat_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p159_eat_proof_auto.
  Include p159_eat_proof_manual.
End VC_Correctness.

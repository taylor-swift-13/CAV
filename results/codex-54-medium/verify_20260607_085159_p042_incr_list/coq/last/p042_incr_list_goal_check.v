From SimpleC.EE.humaneval Require Import p042_incr_list_goal p042_incr_list_proof_auto p042_incr_list_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p042_incr_list_proof_auto.
  Include p042_incr_list_proof_manual.
End VC_Correctness.

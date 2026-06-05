From SimpleC.EE.CAV.verify_20260605_004036v_array_none_zero Require Import array_none_zero_goal array_none_zero_proof_auto array_none_zero_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_none_zero_proof_auto.
  Include array_none_zero_proof_manual.
End VC_Correctness.

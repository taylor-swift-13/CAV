From SimpleC.EE.CAV.verify_20260604_210529v_array_any_zero Require Import array_any_zero_goal array_any_zero_proof_auto array_any_zero_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_any_zero_proof_auto.
  Include array_any_zero_proof_manual.
End VC_Correctness.

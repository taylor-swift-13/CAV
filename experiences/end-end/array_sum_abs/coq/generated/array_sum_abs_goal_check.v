From SimpleC.EE.CAV.verify_20260605_005812v_array_sum_abs Require Import array_sum_abs_goal array_sum_abs_proof_auto array_sum_abs_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_sum_abs_proof_auto.
  Include array_sum_abs_proof_manual.
End VC_Correctness.

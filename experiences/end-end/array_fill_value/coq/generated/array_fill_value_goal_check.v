From SimpleC.EE.CAV.verify_20260605_001513v_array_fill_value Require Import array_fill_value_goal array_fill_value_proof_auto array_fill_value_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_fill_value_proof_auto.
  Include array_fill_value_proof_manual.
End VC_Correctness.

From SimpleC.EE.CAV.verify_20260605_001431v_array_count_odd Require Import array_count_odd_goal array_count_odd_proof_auto array_count_odd_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_count_odd_proof_auto.
  Include array_count_odd_proof_manual.
End VC_Correctness.

From SimpleC.EE.CAV.verify_20260605_004203v_array_product_small Require Import array_product_small_goal array_product_small_proof_auto array_product_small_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_product_small_proof_auto.
  Include array_product_small_proof_manual.
End VC_Correctness.

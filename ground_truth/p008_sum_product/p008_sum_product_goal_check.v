From SimpleC.EE.CAV.ground_truth_p008_sum_product Require Import p008_sum_product_goal p008_sum_product_proof_auto p008_sum_product_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p008_sum_product_proof_auto.
  Include p008_sum_product_proof_manual.
End VC_Correctness.

From SimpleC.EE.CAV.ground_truth_p128_prod_signs Require Import p128_prod_signs_goal p128_prod_signs_proof_auto p128_prod_signs_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p128_prod_signs_proof_auto.
  Include p128_prod_signs_proof_manual.
End VC_Correctness.

From SimpleC.EE.CAV.ground_truth_p025_factorize Require Import p025_factorize_goal p025_factorize_proof_auto p025_factorize_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p025_factorize_proof_auto.
  Include p025_factorize_proof_manual.
End VC_Correctness.

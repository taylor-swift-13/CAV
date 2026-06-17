From SimpleC.EE.CAV.ground_truth_p104_unique_digits Require Import p104_unique_digits_goal p104_unique_digits_proof_auto p104_unique_digits_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p104_unique_digits_proof_auto.
  Include p104_unique_digits_proof_manual.
End VC_Correctness.

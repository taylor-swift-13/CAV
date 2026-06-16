From SimpleC.EE.CAV.verify_20260606_181116_p003_below_zero Require Import p003_below_zero_goal p003_below_zero_proof_auto p003_below_zero_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p003_below_zero_proof_auto.
  Include p003_below_zero_proof_manual.
End VC_Correctness.

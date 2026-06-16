From SimpleC.EE.CAV.verify_20260607_164055_p142_sum_squares Require Import p142_sum_squares_goal p142_sum_squares_proof_auto p142_sum_squares_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p142_sum_squares_proof_auto.
  Include p142_sum_squares_proof_manual.
End VC_Correctness.

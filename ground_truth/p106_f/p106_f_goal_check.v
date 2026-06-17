From SimpleC.EE.CAV.ground_truth_p106_f Require Import p106_f_goal p106_f_proof_auto p106_f_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p106_f_proof_auto.
  Include p106_f_proof_manual.
End VC_Correctness.

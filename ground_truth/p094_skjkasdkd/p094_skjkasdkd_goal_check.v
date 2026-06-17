From SimpleC.EE.CAV.ground_truth_p094_skjkasdkd Require Import p094_skjkasdkd_goal p094_skjkasdkd_proof_auto p094_skjkasdkd_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p094_skjkasdkd_proof_auto.
  Include p094_skjkasdkd_proof_manual.
End VC_Correctness.

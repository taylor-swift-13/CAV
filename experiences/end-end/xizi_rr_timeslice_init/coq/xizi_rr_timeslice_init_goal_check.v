From SimpleC.EE.CAV.verify_20260603_183100v_xizi_rr_timeslice_init Require Import xizi_rr_timeslice_init_goal xizi_rr_timeslice_init_proof_auto xizi_rr_timeslice_init_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include xizi_rr_timeslice_init_proof_auto.
  Include xizi_rr_timeslice_init_proof_manual.
End VC_Correctness.

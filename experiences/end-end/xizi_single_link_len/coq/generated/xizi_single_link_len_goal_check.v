From SimpleC.EE.CAV.verify_20260603_193124v_xizi_single_link_len Require Import xizi_single_link_len_goal xizi_single_link_len_proof_auto xizi_single_link_len_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include xizi_single_link_len_proof_auto.
  Include xizi_single_link_len_proof_manual.
End VC_Correctness.

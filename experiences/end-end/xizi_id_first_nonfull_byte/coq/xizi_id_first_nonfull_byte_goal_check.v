From SimpleC.EE.CAV.verify_20260603_190108v_xizi_id_first_nonfull_byte Require Import xizi_id_first_nonfull_byte_goal xizi_id_first_nonfull_byte_proof_auto xizi_id_first_nonfull_byte_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include xizi_id_first_nonfull_byte_proof_auto.
  Include xizi_id_first_nonfull_byte_proof_manual.
End VC_Correctness.

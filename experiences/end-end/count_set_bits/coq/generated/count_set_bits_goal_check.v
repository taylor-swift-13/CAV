From SimpleC.EE.CAV.verify_20260605_055926v_count_set_bits Require Import count_set_bits_goal count_set_bits_proof_auto count_set_bits_proof_manual.

Module VC_Correctness : VC_Correct.
  Include count_set_bits_proof_auto.
  Include count_set_bits_proof_manual.
End VC_Correctness.

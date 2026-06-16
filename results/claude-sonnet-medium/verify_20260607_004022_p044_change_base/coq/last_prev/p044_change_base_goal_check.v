From SimpleC.EE Require Import p044_change_base_goal p044_change_base_proof_auto p044_change_base_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p044_change_base_proof_auto.
  Include p044_change_base_proof_manual.
End VC_Correctness.

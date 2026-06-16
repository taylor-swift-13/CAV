From SimpleC.EE.CAV.verify_20260607_101730_p064_vowels_count Require Import p064_vowels_count_goal p064_vowels_count_proof_auto p064_vowels_count_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p064_vowels_count_proof_auto.
  Include p064_vowels_count_proof_manual.
End VC_Correctness.

From SimpleC.EE.CAV.ground_truth_p118_get_closest_vowel Require Import p118_get_closest_vowel_goal p118_get_closest_vowel_proof_auto p118_get_closest_vowel_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p118_get_closest_vowel_proof_auto.
  Include p118_get_closest_vowel_proof_manual.
End VC_Correctness.

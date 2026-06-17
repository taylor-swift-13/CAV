From SimpleC.EE.CAV.ground_truth_p051_remove_vowels Require Import p051_remove_vowels_goal p051_remove_vowels_proof_auto p051_remove_vowels_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p051_remove_vowels_proof_auto.
  Include p051_remove_vowels_proof_manual.
End VC_Correctness.

From SimpleC.EE.CAV.ground_truth_p143_words_in_sentence Require Import p143_words_in_sentence_goal p143_words_in_sentence_proof_auto p143_words_in_sentence_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p143_words_in_sentence_proof_auto.
  Include p143_words_in_sentence_proof_manual.
End VC_Correctness.

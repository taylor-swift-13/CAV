From SimpleC.EE.CAV.ground_truth_p007_filter_by_substring Require Import p007_filter_by_substring_goal p007_filter_by_substring_proof_auto p007_filter_by_substring_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include p007_filter_by_substring_proof_auto.
  Include p007_filter_by_substring_proof_manual.
End VC_Correctness.

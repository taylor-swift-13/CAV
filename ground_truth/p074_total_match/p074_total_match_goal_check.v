From SimpleC.EE.CAV.ground_truth_p074_total_match Require Import p074_total_match_goal p074_total_match_proof_auto p074_total_match_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include p074_total_match_proof_auto.
  Include p074_total_match_proof_manual.
End VC_Correctness.

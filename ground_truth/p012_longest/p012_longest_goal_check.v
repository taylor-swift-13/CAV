From SimpleC.EE.CAV.ground_truth_p012_longest Require Import p012_longest_goal p012_longest_proof_auto p012_longest_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include p012_longest_proof_auto.
  Include p012_longest_proof_manual.
End VC_Correctness.

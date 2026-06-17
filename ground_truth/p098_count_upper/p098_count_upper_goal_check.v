From SimpleC.EE.CAV.ground_truth_p098_count_upper Require Import p098_count_upper_goal p098_count_upper_proof_auto p098_count_upper_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p098_count_upper_proof_auto.
  Include p098_count_upper_proof_manual.
End VC_Correctness.

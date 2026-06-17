From SimpleC.EE.CAV.ground_truth_p091_is_bored Require Import p091_is_bored_goal p091_is_bored_proof_auto p091_is_bored_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p091_is_bored_proof_auto.
  Include p091_is_bored_proof_manual.
End VC_Correctness.

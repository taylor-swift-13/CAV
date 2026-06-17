From SimpleC.EE.CAV.ground_truth_p086_anti_shuffle Require Import p086_anti_shuffle_goal p086_anti_shuffle_proof_auto p086_anti_shuffle_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p086_anti_shuffle_proof_auto.
  Include p086_anti_shuffle_proof_manual.
End VC_Correctness.

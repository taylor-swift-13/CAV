From SimpleC.EE.CAV.ground_truth_p103_rounded_avg Require Import p103_rounded_avg_goal p103_rounded_avg_proof_auto p103_rounded_avg_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p103_rounded_avg_proof_auto.
  Include p103_rounded_avg_proof_manual.
End VC_Correctness.

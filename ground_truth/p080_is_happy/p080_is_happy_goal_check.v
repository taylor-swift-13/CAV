From SimpleC.EE.CAV.ground_truth_p080_is_happy Require Import p080_is_happy_goal p080_is_happy_proof_auto p080_is_happy_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p080_is_happy_proof_auto.
  Include p080_is_happy_proof_manual.
End VC_Correctness.

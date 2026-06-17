From SimpleC.EE.CAV.ground_truth_p023_strlen Require Import p023_strlen_goal p023_strlen_proof_auto p023_strlen_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p023_strlen_proof_auto.
  Include p023_strlen_proof_manual.
End VC_Correctness.

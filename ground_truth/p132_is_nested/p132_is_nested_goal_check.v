From SimpleC.EE.CAV.ground_truth_p132_is_nested Require Import p132_is_nested_goal p132_is_nested_proof_auto p132_is_nested_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p132_is_nested_proof_auto.
  Include p132_is_nested_proof_manual.
End VC_Correctness.

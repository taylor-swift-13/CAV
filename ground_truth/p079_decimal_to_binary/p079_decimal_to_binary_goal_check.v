From SimpleC.EE.CAV.ground_truth_p079_decimal_to_binary Require Import p079_decimal_to_binary_goal p079_decimal_to_binary_proof_auto p079_decimal_to_binary_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p079_decimal_to_binary_proof_auto.
  Include p079_decimal_to_binary_proof_manual.
End VC_Correctness.

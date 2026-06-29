From SimpleC.EE.CAV.ground_truth_p028_concatenate Require Import p028_concatenate_goal p028_concatenate_proof_auto p028_concatenate_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include p028_concatenate_proof_auto.
  Include p028_concatenate_proof_manual.
End VC_Correctness.

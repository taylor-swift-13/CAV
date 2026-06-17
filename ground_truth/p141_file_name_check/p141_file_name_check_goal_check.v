From SimpleC.EE.CAV.ground_truth_p141_file_name_check Require Import p141_file_name_check_goal p141_file_name_check_proof_auto p141_file_name_check_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p141_file_name_check_proof_auto.
  Include p141_file_name_check_proof_manual.
End VC_Correctness.

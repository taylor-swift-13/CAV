From SimpleC.EE.CAV.ground_truth_p124_valid_date Require Import p124_valid_date_goal p124_valid_date_proof_auto p124_valid_date_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p124_valid_date_proof_auto.
  Include p124_valid_date_proof_manual.
End VC_Correctness.

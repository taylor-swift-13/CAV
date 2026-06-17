From SimpleC.EE.CAV.ground_truth_p119_match_parens Require Import p119_match_parens_goal p119_match_parens_proof_auto p119_match_parens_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p119_match_parens_proof_auto.
  Include p119_match_parens_proof_manual.
End VC_Correctness.

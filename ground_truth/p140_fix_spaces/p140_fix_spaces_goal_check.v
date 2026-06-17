From SimpleC.EE.CAV.ground_truth_p140_fix_spaces Require Import p140_fix_spaces_goal p140_fix_spaces_proof_auto p140_fix_spaces_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p140_fix_spaces_proof_auto.
  Include p140_fix_spaces_proof_manual.
End VC_Correctness.

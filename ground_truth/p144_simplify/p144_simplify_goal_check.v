From SimpleC.EE.CAV.ground_truth_p144_simplify Require Import p144_simplify_goal p144_simplify_proof_auto p144_simplify_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p144_simplify_proof_auto.
  Include p144_simplify_proof_manual.
End VC_Correctness.

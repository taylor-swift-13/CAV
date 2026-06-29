From SimpleC.EE.CAV.ground_truth_p029_filter_by_prefix Require Import p029_filter_by_prefix_goal p029_filter_by_prefix_proof_auto p029_filter_by_prefix_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include p029_filter_by_prefix_proof_auto.
  Include p029_filter_by_prefix_proof_manual.
End VC_Correctness.

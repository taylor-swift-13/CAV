From SimpleC.EE.CAV.ground_truth_p014_all_prefixes Require Import p014_all_prefixes_goal p014_all_prefixes_proof_auto p014_all_prefixes_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include p014_all_prefixes_proof_auto.
  Include p014_all_prefixes_proof_manual.
End VC_Correctness.

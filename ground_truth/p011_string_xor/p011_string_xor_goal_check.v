From SimpleC.EE.CAV.ground_truth_p011_string_xor Require Import p011_string_xor_goal p011_string_xor_proof_auto p011_string_xor_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p011_string_xor_proof_auto.
  Include p011_string_xor_proof_manual.
End VC_Correctness.

From SimpleC.EE.CAV.ground_truth_p054_same_chars Require Import p054_same_chars_goal p054_same_chars_proof_auto p054_same_chars_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p054_same_chars_proof_auto.
  Include p054_same_chars_proof_manual.
End VC_Correctness.

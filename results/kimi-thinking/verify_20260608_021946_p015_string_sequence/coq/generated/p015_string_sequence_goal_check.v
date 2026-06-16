From SimpleC.EE.CAV.verify_20260608_021946_p015_string_sequence Require Import p015_string_sequence_goal p015_string_sequence_proof_auto p015_string_sequence_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p015_string_sequence_proof_auto.
  Include p015_string_sequence_proof_manual.
End VC_Correctness.

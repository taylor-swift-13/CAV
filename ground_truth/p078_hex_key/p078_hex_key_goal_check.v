From SimpleC.EE.CAV.ground_truth_p078_hex_key Require Import p078_hex_key_goal p078_hex_key_proof_auto p078_hex_key_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p078_hex_key_proof_auto.
  Include p078_hex_key_proof_manual.
End VC_Correctness.

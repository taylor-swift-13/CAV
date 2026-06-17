From SimpleC.EE.CAV.ground_truth_p089_encrypt Require Import p089_encrypt_goal p089_encrypt_proof_auto p089_encrypt_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p089_encrypt_proof_auto.
  Include p089_encrypt_proof_manual.
End VC_Correctness.

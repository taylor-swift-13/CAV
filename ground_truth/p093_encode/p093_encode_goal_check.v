From SimpleC.EE.CAV.ground_truth_p093_encode Require Import p093_encode_goal p093_encode_proof_auto p093_encode_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p093_encode_proof_auto.
  Include p093_encode_proof_manual.
End VC_Correctness.

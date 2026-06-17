From SimpleC.EE.CAV.ground_truth_p050_decode_shift Require Import p050_decode_shift_goal p050_decode_shift_proof_auto p050_decode_shift_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p050_decode_shift_proof_auto.
  Include p050_decode_shift_proof_manual.
End VC_Correctness.

From SimpleC.EE.CAV.ground_truth_p065_circular_shift Require Import p065_circular_shift_goal p065_circular_shift_proof_auto p065_circular_shift_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p065_circular_shift_proof_auto.
  Include p065_circular_shift_proof_manual.
End VC_Correctness.

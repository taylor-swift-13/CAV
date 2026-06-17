From SimpleC.EE.CAV.ground_truth_p038_decode_cyclic Require Import p038_decode_cyclic_goal p038_decode_cyclic_proof_auto p038_decode_cyclic_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p038_decode_cyclic_proof_auto.
  Include p038_decode_cyclic_proof_manual.
End VC_Correctness.

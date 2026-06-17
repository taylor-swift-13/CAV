From SimpleC.EE.CAV.ground_truth_p018_how_many_times Require Import p018_how_many_times_goal p018_how_many_times_proof_auto p018_how_many_times_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p018_how_many_times_proof_auto.
  Include p018_how_many_times_proof_manual.
End VC_Correctness.

From SimpleC.EE.CAV.ground_truth_p102_choose_num Require Import p102_choose_num_goal p102_choose_num_proof_auto p102_choose_num_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p102_choose_num_proof_auto.
  Include p102_choose_num_proof_manual.
End VC_Correctness.

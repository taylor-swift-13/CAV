From SimpleC.EE.CAV.ground_truth_p150_x_or_y Require Import p150_x_or_y_goal p150_x_or_y_proof_auto p150_x_or_y_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p150_x_or_y_proof_auto.
  Include p150_x_or_y_proof_manual.
End VC_Correctness.

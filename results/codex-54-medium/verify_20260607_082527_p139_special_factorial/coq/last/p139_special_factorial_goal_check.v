From SimpleC.EE.humaneval Require Import p139_special_factorial_goal p139_special_factorial_proof_auto p139_special_factorial_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p139_special_factorial_proof_auto.
  Include p139_special_factorial_proof_manual.
End VC_Correctness.

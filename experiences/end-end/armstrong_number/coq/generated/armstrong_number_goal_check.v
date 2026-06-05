From SimpleC.EE.CAV.verify_20260605_162851v_armstrong_number Require Import armstrong_number_goal armstrong_number_proof_auto armstrong_number_proof_manual.

Module VC_Correctness : VC_Correct.
  Include armstrong_number_proof_auto.
  Include armstrong_number_proof_manual.
End VC_Correctness.

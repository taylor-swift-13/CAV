From SimpleC.EE.QCP_demos_LLM Require Import p131_digits_goal p131_digits_proof_auto p131_digits_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p131_digits_proof_auto.
  Include p131_digits_proof_manual.
End VC_Correctness.

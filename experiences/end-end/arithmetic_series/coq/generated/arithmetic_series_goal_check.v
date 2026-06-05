From SimpleC.EE.CAV.verify_20260604_165821_arithmetic_series Require Import arithmetic_series_goal arithmetic_series_proof_auto arithmetic_series_proof_manual.

Module VC_Correctness : VC_Correct.
  Include arithmetic_series_proof_auto.
  Include arithmetic_series_proof_manual.
End VC_Correctness.

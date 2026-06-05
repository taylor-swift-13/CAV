From SimpleC.EE.CAV.verify_20260604_105149_leap_year Require Import leap_year_goal leap_year_proof_auto leap_year_proof_manual.

Module VC_Correctness : VC_Correct.
  Include leap_year_proof_auto.
  Include leap_year_proof_manual.
End VC_Correctness.

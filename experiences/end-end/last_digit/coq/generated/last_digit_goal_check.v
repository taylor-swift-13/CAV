From SimpleC.EE.CAV.verify_20260604_104545_last_digit Require Import last_digit_goal last_digit_proof_auto last_digit_proof_manual.

Module VC_Correctness : VC_Correct.
  Include last_digit_proof_auto.
  Include last_digit_proof_manual.
End VC_Correctness.

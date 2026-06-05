From SimpleC.EE.CAV.verify_20260604_162058_add_digits Require Import add_digits_goal add_digits_proof_auto add_digits_proof_manual.

Module VC_Correctness : VC_Correct.
  Include add_digits_proof_auto.
  Include add_digits_proof_manual.
End VC_Correctness.

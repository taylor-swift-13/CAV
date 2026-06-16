From SimpleC.EE.CAV.verify_20260607_013317_p010_make_palindrome Require Import p010_make_palindrome_goal p010_make_palindrome_proof_auto p010_make_palindrome_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p010_make_palindrome_proof_auto.
  Include p010_make_palindrome_proof_manual.
End VC_Correctness.

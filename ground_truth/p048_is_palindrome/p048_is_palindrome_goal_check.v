From SimpleC.EE.CAV.ground_truth_p048_is_palindrome Require Import p048_is_palindrome_goal p048_is_palindrome_proof_auto p048_is_palindrome_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p048_is_palindrome_proof_auto.
  Include p048_is_palindrome_proof_manual.
End VC_Correctness.

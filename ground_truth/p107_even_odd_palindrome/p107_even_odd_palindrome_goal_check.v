From SimpleC.EE.CAV.ground_truth_p107_even_odd_palindrome Require Import p107_even_odd_palindrome_goal p107_even_odd_palindrome_proof_auto p107_even_odd_palindrome_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p107_even_odd_palindrome_proof_auto.
  Include p107_even_odd_palindrome_proof_manual.
End VC_Correctness.

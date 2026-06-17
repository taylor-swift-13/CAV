From SimpleC.EE.CAV.ground_truth_p069_search Require Import p069_search_goal p069_search_proof_auto p069_search_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p069_search_proof_auto.
  Include p069_search_proof_manual.
End VC_Correctness.

From SimpleC.EE.CAV.verify_20260605_002002v_array_index_of_max Require Import array_index_of_max_goal array_index_of_max_proof_auto array_index_of_max_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_index_of_max_proof_auto.
  Include array_index_of_max_proof_manual.
End VC_Correctness.

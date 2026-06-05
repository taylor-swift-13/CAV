From SimpleC.EE.CAV.verify_20260604_201124v_array_all_even Require Import array_all_even_goal array_all_even_proof_auto array_all_even_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include array_all_even_proof_auto.
  Include array_all_even_proof_manual.
End VC_Correctness.

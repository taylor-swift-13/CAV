From SimpleC.EE.CAV.verify_20260607_140907_p122_add_elements Require Import p122_add_elements_goal p122_add_elements_proof_auto p122_add_elements_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p122_add_elements_proof_auto.
  Include p122_add_elements_proof_manual.
End VC_Correctness.

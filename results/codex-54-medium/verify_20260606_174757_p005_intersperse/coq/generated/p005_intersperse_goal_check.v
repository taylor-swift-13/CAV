From SimpleC.EE.CAV.verify_20260606_174757_p005_intersperse Require Import p005_intersperse_goal p005_intersperse_proof_auto p005_intersperse_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p005_intersperse_proof_auto.
  Include p005_intersperse_proof_manual.
End VC_Correctness.

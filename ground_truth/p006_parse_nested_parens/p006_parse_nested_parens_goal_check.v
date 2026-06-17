From SimpleC.EE.CAV.ground_truth_p006_parse_nested_parens Require Import p006_parse_nested_parens_goal p006_parse_nested_parens_proof_auto p006_parse_nested_parens_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p006_parse_nested_parens_proof_auto.
  Include p006_parse_nested_parens_proof_manual.
End VC_Correctness.

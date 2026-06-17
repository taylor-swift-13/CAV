From SimpleC.EE.CAV.ground_truth_p017_parse_music Require Import p017_parse_music_goal p017_parse_music_proof_auto p017_parse_music_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p017_parse_music_proof_auto.
  Include p017_parse_music_proof_manual.
End VC_Correctness.

From SimpleC.EE.CAV.ground_truth_p109_move_one_ball Require Import p109_move_one_ball_goal p109_move_one_ball_proof_auto p109_move_one_ball_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p109_move_one_ball_proof_auto.
  Include p109_move_one_ball_proof_manual.
End VC_Correctness.

From SimpleC.EE.CAV.ground_truth_p121_solutions Require Import p121_solutions_goal p121_solutions_proof_auto p121_solutions_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p121_solutions_proof_auto.
  Include p121_solutions_proof_manual.
End VC_Correctness.

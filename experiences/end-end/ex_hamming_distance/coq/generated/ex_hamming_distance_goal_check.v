From SimpleC.EE.CAV.verify_20260605_080838v_ex_hamming_distance Require Import ex_hamming_distance_goal ex_hamming_distance_proof_auto ex_hamming_distance_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include ex_hamming_distance_proof_auto.
  Include ex_hamming_distance_proof_manual.
End VC_Correctness.

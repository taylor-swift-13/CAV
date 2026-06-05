From SimpleC.EE.CAV.verify_20260605_075354v_ex_darts_score Require Import ex_darts_score_goal ex_darts_score_proof_auto ex_darts_score_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ex_darts_score_proof_auto.
  Include ex_darts_score_proof_manual.
End VC_Correctness.

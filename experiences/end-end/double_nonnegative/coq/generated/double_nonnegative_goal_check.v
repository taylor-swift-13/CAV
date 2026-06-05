From SimpleC.EE.CAV.verify_20260605_063324v_double_nonnegative Require Import double_nonnegative_goal double_nonnegative_proof_auto double_nonnegative_proof_manual.

Module VC_Correctness : VC_Correct.
  Include double_nonnegative_proof_auto.
  Include double_nonnegative_proof_manual.
End VC_Correctness.

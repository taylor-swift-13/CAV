From SimpleC.EE.CAV.verify_20260605_073258v_ex_collatz_steps Require Import ex_collatz_steps_goal ex_collatz_steps_proof_auto ex_collatz_steps_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ex_collatz_steps_proof_auto.
  Include ex_collatz_steps_proof_manual.
End VC_Correctness.

From SimpleC.EE.CAV.verify_20260608_1701043326_p046_fib4 Require Import p046_fib4_goal p046_fib4_proof_auto p046_fib4_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p046_fib4_proof_auto.
  Include p046_fib4_proof_manual.
End VC_Correctness.

From SimpleC.EE.CAV.ground_truth_p055_fib Require Import p055_fib_goal p055_fib_proof_auto p055_fib_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p055_fib_proof_auto.
  Include p055_fib_proof_manual.
End VC_Correctness.

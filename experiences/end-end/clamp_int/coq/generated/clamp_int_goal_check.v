From SimpleC.EE.CAV.verify_20260604_104812_clamp_int Require Import clamp_int_goal clamp_int_proof_auto clamp_int_proof_manual.

Module VC_Correctness : VC_Correct.
  Include clamp_int_proof_auto.
  Include clamp_int_proof_manual.
End VC_Correctness.

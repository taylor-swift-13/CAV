From SimpleC.EE.CAV.verify_20260604_104352_is_even Require Import is_even_goal is_even_proof_auto is_even_proof_manual.

Module VC_Correctness : VC_Correct.
  Include is_even_proof_auto.
  Include is_even_proof_manual.
End VC_Correctness.

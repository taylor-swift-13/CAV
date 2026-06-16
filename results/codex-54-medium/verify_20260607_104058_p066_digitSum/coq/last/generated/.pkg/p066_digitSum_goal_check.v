From SimpleC.EE.CAV.verify_20260607_104058_p066_digitSum Require Import p066_digitSum_goal p066_digitSum_proof_auto p066_digitSum_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p066_digitSum_proof_auto.
  Include p066_digitSum_proof_manual.
End VC_Correctness.

From SimpleC.EE.CAV.ground_truth_p027_filp_case Require Import p027_filp_case_goal p027_filp_case_proof_auto p027_filp_case_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p027_filp_case_proof_auto.
  Include p027_filp_case_proof_manual.
End VC_Correctness.

From SimpleC.EE.CAV.ground_truth_p095_check_dict_case Require Import p095_check_dict_case_goal p095_check_dict_case_proof_auto p095_check_dict_case_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include p095_check_dict_case_proof_auto.
  Include p095_check_dict_case_proof_manual.
End VC_Correctness.

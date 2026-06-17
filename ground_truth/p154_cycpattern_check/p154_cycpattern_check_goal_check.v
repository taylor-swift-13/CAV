From SimpleC.EE.CAV.ground_truth_p154_cycpattern_check Require Import p154_cycpattern_check_goal p154_cycpattern_check_proof_auto p154_cycpattern_check_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include p154_cycpattern_check_proof_auto.
  Include p154_cycpattern_check_proof_manual.
End VC_Correctness.

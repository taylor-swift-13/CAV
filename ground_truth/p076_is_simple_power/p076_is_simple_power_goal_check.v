From SimpleC.EE.CAV.ground_truth_p076_is_simple_power Require Import p076_is_simple_power_goal p076_is_simple_power_proof_auto p076_is_simple_power_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p076_is_simple_power_proof_auto.
  Include p076_is_simple_power_proof_manual.
End VC_Correctness.

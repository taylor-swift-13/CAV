From SimpleC.EE.CAV.verify_20260607_111713_p114_minSubArraySum Require Import p114_minSubArraySum_goal p114_minSubArraySum_proof_auto p114_minSubArraySum_proof_manual.

Module VC_Correctness : VC_Correct.
  Include long_array_strategy_proof.
  Include p114_minSubArraySum_proof_auto.
  Include p114_minSubArraySum_proof_manual.
End VC_Correctness.

From SimpleC.EE.CAV.verify_20260607_152224_p072_will_it_fly Require Import p072_will_it_fly_goal p072_will_it_fly_proof_auto p072_will_it_fly_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p072_will_it_fly_proof_auto.
  Include p072_will_it_fly_proof_manual.
End VC_Correctness.

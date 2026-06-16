From SimpleC.EE.CAV.verify_20260607_092540_p063_fibfib Require Import p063_fibfib_goal p063_fibfib_proof_auto p063_fibfib_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p063_fibfib_proof_auto.
  Include p063_fibfib_proof_manual.
End VC_Correctness.

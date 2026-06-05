From SimpleC.EE.CAV.verify_20260605_062321v_digit_product Require Import digit_product_goal digit_product_proof_auto digit_product_proof_manual.

Module VC_Correctness : VC_Correct.
  Include digit_product_proof_auto.
  Include digit_product_proof_manual.
End VC_Correctness.

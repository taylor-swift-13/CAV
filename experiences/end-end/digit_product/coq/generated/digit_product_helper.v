Require Import ZArith.
Require Import digit_product.

Open Scope Z_scope.

Definition digit_product_acc_z (n acc : Z) : Z :=
  digit_product_loop_fuel n acc (Z.to_nat n).

Definition digit_product_safe_z (n acc : Z) : Prop :=
  digit_product_safe_fuel n acc (Z.to_nat n).

Require Import ZArith.
Require Import armstrong_number.

Open Scope Z_scope.

Definition zpow_nat_z (base exp : Z) : Z :=
  zpow_nat base (Z.to_nat exp).

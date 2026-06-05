Require Import ZArith.

Open Scope Z_scope.

Fixpoint aliquot_sum_from_fuel_tail (n d : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      if Z.geb d n then
        0
      else
        (if Z.eqb (Z.rem n d) 0 then d else 0) +
        aliquot_sum_from_fuel_tail n (d + 1) fuel'
  end.

Definition aliquot_sum_tail_z (n d : Z) : Z :=
  aliquot_sum_from_fuel_tail n d (Z.to_nat (n - d + 1)).

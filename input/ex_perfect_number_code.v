Require Import ZArith.

Open Scope Z_scope.

Fixpoint aliquot_sum_from_fuel (n d : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      if Z.geb d n then
        0
      else
        (if Z.eqb (Z.rem n d) 0 then d else 0) +
        aliquot_sum_from_fuel n (d + 1) fuel'
  end.

Definition aliquot_sum_z (n : Z) : Z :=
  aliquot_sum_from_fuel n 1 (Z.to_nat n).

Definition ex_perfect_number_code_spec (n r : Z) : Prop :=
  r =
  if Z.eqb (aliquot_sum_z n) n then
    1
  else if Z.gtb (aliquot_sum_z n) n then
    2
  else
    3.

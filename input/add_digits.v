Require Import ZArith.

Open Scope Z_scope.

Fixpoint digit_sum_fuel (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S k =>
      if Z.leb n 0 then
        0
      else
        Z.rem n 10 + digit_sum_fuel (Z.div n 10) k
  end.

Definition digit_sum_aux (n : Z) : Z :=
  digit_sum_fuel n (Z.to_nat n).

Fixpoint digital_root_fuel (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S k =>
      if Z.leb n 9 then n
      else digital_root_fuel (digit_sum_aux n) k
  end.

Definition digital_root_z (n : Z) : Z :=
  digital_root_fuel n (Z.to_nat n).

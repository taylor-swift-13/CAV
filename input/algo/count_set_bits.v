Require Import ZArith.

Open Scope Z_scope.

Fixpoint count_set_bits_fuel (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S k =>
      if Z.leb n 0 then
        0
      else
        Z.rem n 2 + count_set_bits_fuel (Z.div n 2) k
  end.

Definition count_set_bits_z (n : Z) : Z :=
  count_set_bits_fuel n (Z.to_nat n).

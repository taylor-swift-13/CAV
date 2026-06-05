Require Import ZArith.

Open Scope Z_scope.

Fixpoint zpow_nat (base : Z) (exp : nat) : Z :=
  match exp with
  | O => 1
  | S k => base * zpow_nat base k
  end.

Fixpoint count_digits_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S k =>
    if Z.eqb n 0 then 0
    else 1 + count_digits_aux (Z.div n 10) k
  end.

Definition count_digits_z (n : Z) : Z :=
  if Z.eqb n 0 then 1
  else count_digits_aux n (S (Z.to_nat n)).

Fixpoint armstrong_sum_aux (n : Z) (d : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S k =>
    if Z.eqb n 0 then 0
    else
      zpow_nat (Z.modulo n 10) (Z.to_nat d) +
      armstrong_sum_aux (Z.div n 10) d k
  end.

Definition armstrong_sum_z (n : Z) (d : Z) : Z :=
  armstrong_sum_aux n d (S (Z.to_nat n)).

Definition is_armstrong_z (n : Z) : Z :=
  let d := count_digits_z n in
  if Z.eqb (armstrong_sum_z n d) n then 1 else 0.

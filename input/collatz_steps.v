Require Import ZArith.

Open Scope Z_scope.

Definition collatz_next (n : Z) : Z :=
  if Z.even n then Z.div n 2 else 3 * n + 1.

Fixpoint collatz_steps_fuel_nat (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      if Z.eqb n 1 then 0 else 1 + collatz_steps_fuel_nat (collatz_next n) fuel'
  end.

Fixpoint collatz_safe_fuel_nat (n : Z) (fuel : nat) : Prop :=
  match fuel with
  | O => n = 1
  | S fuel' =>
      1 <= n <= 2147483647 /\
      if Z.eqb n 1 then
        True
      else if Z.even n then
        collatz_safe_fuel_nat (Z.div n 2) fuel'
      else
        n <= 715827882 /\ collatz_safe_fuel_nat (3 * n + 1) fuel'
  end.

Definition collatz_steps_fuel (n fuel : Z) : Z :=
  collatz_steps_fuel_nat n (Z.to_nat fuel).

Definition collatz_safe_fuel (n fuel : Z) : Prop :=
  collatz_safe_fuel_nat n (Z.to_nat fuel).

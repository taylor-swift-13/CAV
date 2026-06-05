Require Import ZArith.

Open Scope Z_scope.

Definition ex_collatz_next (n : Z) : Z :=
  if Z.even n then Z.div n 2 else 3 * n + 1.

Fixpoint ex_collatz_steps_fuel_nat (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      if Z.eqb n 1 then 0 else 1 + ex_collatz_steps_fuel_nat (ex_collatz_next n) fuel'
  end.

Fixpoint ex_collatz_safe_fuel_nat (n : Z) (fuel : nat) : Prop :=
  match fuel with
  | O => n = 1
  | S fuel' =>
      1 <= n <= 9223372036854775807 /\
      if Z.eqb n 1 then
        True
      else if Z.even n then
        ex_collatz_safe_fuel_nat (Z.div n 2) fuel'
      else
        n <= 3074457345618258602 /\ ex_collatz_safe_fuel_nat (3 * n + 1) fuel'
  end.

Definition ex_collatz_steps_fuel (n fuel : Z) : Z :=
  ex_collatz_steps_fuel_nat n (Z.to_nat fuel).

Definition ex_collatz_safe_fuel (n fuel : Z) : Prop :=
  ex_collatz_safe_fuel_nat n (Z.to_nat fuel).

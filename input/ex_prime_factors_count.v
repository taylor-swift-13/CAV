Require Import ZArith.

Open Scope Z_scope.

Fixpoint ex_prime_factors_count_go (n d : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      if Z.leb n 1 then
        0
      else if Z.leb (d * d) n then
        if Z.eqb (Z.rem n d) 0 then
          1 + ex_prime_factors_count_go (Z.div n d) d fuel'
        else
          ex_prime_factors_count_go n (d + 1) fuel'
      else
        1
  end.

Definition ex_prime_factors_count_spec (n : Z) : Z :=
  ex_prime_factors_count_go n 2 (Z.to_nat n).

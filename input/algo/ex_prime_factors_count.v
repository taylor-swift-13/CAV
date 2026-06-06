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
  let '(_, _, count) := Z.iter n
    (fun st =>
       let '(cur, d, count) := st in
       if Z.leb cur 1 then (cur, d, count)
       else
         if Z.leb (d * d) cur then
           if Z.eqb (Z.rem cur d) 0
           then (Z.div cur d, d, count + 1)
           else (cur, d + 1, count)
         else (1, d, count + 1))
    (n, 2, 0) in
  count.

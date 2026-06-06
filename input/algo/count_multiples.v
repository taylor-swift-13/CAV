Require Import ZArith.

Open Scope Z_scope.

Fixpoint count_multiples_upto (k : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S n =>
      count_multiples_upto k n +
      (if Z.eq_dec (Z.rem (Z.of_nat (S n)) k) 0 then 1 else 0)
  end.

Definition count_multiples_spec (n k : Z) : Z :=
  snd (Z.iter n
    (fun st =>
       let '(x, count) := st in
       let x' := x + 1 in
       (x', count + if Z.eq_dec (Z.rem x' k) 0 then 1 else 0))
    (0, 0)).

Require Import ZArith.

Open Scope Z_scope.

Fixpoint count_divisors_upto (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S k =>
      count_divisors_upto n k +
      (if Z.eq_dec (Z.rem n (Z.of_nat (S k))) 0 then 1 else 0)
  end.

Definition count_divisors_spec (n : Z) : Z :=
  snd (Z.iter n
    (fun st =>
       let '(d, count) := st in
       let d' := d + 1 in
       (d', count + if Z.eq_dec (Z.rem n d') 0 then 1 else 0))
    (0, 0)).

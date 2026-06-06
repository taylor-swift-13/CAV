Require Import ZArith.

Open Scope Z_scope.

Fixpoint digit_product_loop_fuel (n acc : Z) (fuel : nat) : Z :=
  match fuel with
  | O => acc
  | S k =>
      if Z.leb n 0 then
        acc
      else
        digit_product_loop_fuel (Z.div n 10) (acc * Z.rem n 10) k
  end.

Fixpoint digit_product_safe_fuel (n acc : Z) (fuel : nat) : Prop :=
  match fuel with
  | O => True
  | S k =>
      if Z.leb n 0 then
        True
      else
        let acc' := acc * Z.rem n 10 in
        (-2147483648 <= acc' <= 2147483647) /\
        digit_product_safe_fuel (Z.div n 10) acc' k
  end.

Definition digit_product_z (n : Z) : Z :=
  if Z.leb n 0 then
    0
  else
    snd (Z.iter n
      (fun st =>
         let '(cur, acc) := st in
         if Z.leb cur 0 then (cur, acc)
         else (Z.div cur 10, acc * Z.rem cur 10))
      (n, 1)).

Definition digit_product_pre_z (n : Z) : Prop :=
  0 <= n /\
  forall i,
    0 <= i <= n ->
    let '(_, acc) := Z.iter i
      (fun st =>
         let '(cur, acc) := st in
         if Z.leb cur 0 then (cur, acc)
         else (Z.div cur 10, acc * Z.rem cur 10))
      (n, 1) in
    -2147483648 <= acc <= 2147483647.

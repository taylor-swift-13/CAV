Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint count_asterisks_between_bars_go (inside : Z) (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs =>
      if Z.eq_dec x 124 then
        count_asterisks_between_bars_go (1 - inside) xs
      else
        (if Z.eq_dec x 42 then
           if Z.eq_dec inside 1 then 1 else 0
         else 0) +
        count_asterisks_between_bars_go inside xs
  end.

Definition count_asterisks_between_bars_spec (l : list Z) : Z :=
  count_asterisks_between_bars_go 0 l.

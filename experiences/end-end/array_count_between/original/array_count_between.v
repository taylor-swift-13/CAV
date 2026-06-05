Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint array_count_between_spec (l : list Z) (lo hi : Z) : Z :=
  match l with
  | nil => 0
  | x :: xs =>
      (if Z_le_dec lo x then
         if Z_le_dec x hi then 1 else 0
       else 0) +
      array_count_between_spec xs lo hi
  end.

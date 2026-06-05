Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint array_count_negative_spec (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs =>
      (if Z_lt_dec x 0 then 1 else 0) + array_count_negative_spec xs
  end.

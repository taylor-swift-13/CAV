Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint array_sum_nonnegative_spec (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs =>
      (if Z_le_dec 0 x then x else 0) + array_sum_nonnegative_spec xs
  end.

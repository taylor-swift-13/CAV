Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint aug_string_count_index_004_spec (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs =>
      (if Z.eq_dec x 101 then 1 else 0) +
      aug_string_count_index_004_spec xs
  end.

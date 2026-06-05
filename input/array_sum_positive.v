Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint array_sum_positive_spec (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs =>
      (if Z_gt_dec x 0 then x else 0) + array_sum_positive_spec xs
  end.

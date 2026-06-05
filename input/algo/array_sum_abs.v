Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Definition sum_abs (l : list Z) : Z :=
  fold_right Z.add 0 (map Z.abs l).

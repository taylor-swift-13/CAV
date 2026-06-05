Require Import Coq.Lists.List.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint product (l : list Z) : Z :=
  match l with
  | [] => 1
  | h :: t => h * product t
  end.

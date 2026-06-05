Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition ex_hamming_distance_pre (a b : list Z) : Prop :=
  Zlength a = Zlength b.

Fixpoint ex_hamming_distance_spec (a b : list Z) : Z :=
  match a, b with
  | [], [] => 0
  | x :: xs, y :: ys =>
      (if Z.eqb x y then 0 else 1) + ex_hamming_distance_spec xs ys
  | _, _ => 0
  end.

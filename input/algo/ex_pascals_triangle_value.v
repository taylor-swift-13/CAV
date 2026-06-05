Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.

Open Scope Z_scope.

Definition ex_pascals_triangle_value_pre (row col : Z) : Prop :=
  0 <= col /\ col <= row /\ row <= 30.

Fixpoint ex_pascals_triangle_value_binom (row col : nat) : Z :=
  match row, col with
  | _, O => 1
  | O, S _ => 0
  | S row', S col' =>
      ex_pascals_triangle_value_binom row' col' +
      ex_pascals_triangle_value_binom row' (S col')
  end.

Definition ex_pascals_triangle_value_spec (row col ret : Z) : Prop :=
  ret = ex_pascals_triangle_value_binom (Z.to_nat row) (Z.to_nat col).


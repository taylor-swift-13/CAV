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

Inductive ex_pascals_triangle_value_z : Z -> Z -> Z -> Prop :=
| pascal_left_edge :
    forall row, 0 <= row -> ex_pascals_triangle_value_z row 0 1
| pascal_right_edge :
    forall row, 0 <= row -> ex_pascals_triangle_value_z row row 1
| pascal_inner :
    forall row col a b,
      0 < col < row ->
      ex_pascals_triangle_value_z (row - 1) (col - 1) a ->
      ex_pascals_triangle_value_z (row - 1) col b ->
      ex_pascals_triangle_value_z row col (a + b).

Definition ex_pascals_triangle_value_spec (row col ret : Z) : Prop :=
  ex_pascals_triangle_value_z row col ret.

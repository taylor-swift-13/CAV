Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Definition xizi_next_at (idx : Z) (nexts : list Z) : Z :=
  nth (Z.to_nat idx) nexts (-1).

Fixpoint xizi_member (x : Z) (xs : list Z) : bool :=
  match xs with
  | nil => false
  | y :: ys => if Z.eq_dec x y then true else xizi_member x ys
  end.

Fixpoint xizi_single_link_valid_nat
    (fuel : nat) (seen : list Z) (node : Z) (nexts : list Z) : Prop :=
  match fuel with
  | O => node = -1
  | S fuel' =>
      if Z.eq_dec node (-1) then True
      else
        0 <= node < Z.of_nat (length nexts) /\
        xizi_member node seen = false /\
        xizi_single_link_valid_nat fuel' (node :: seen) (xizi_next_at node nexts) nexts
  end.

Fixpoint xizi_single_link_len_nat (fuel : nat) (node : Z) (nexts : list Z) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      if Z.eq_dec node (-1) then 0
      else 1 + xizi_single_link_len_nat fuel' (xizi_next_at node nexts) nexts
  end.

Definition xizi_single_link_wf (head : Z) (nexts : list Z) : Prop :=
  0 <= head < Z.of_nat (length nexts) /\
  xizi_single_link_valid_nat
    (Z.to_nat (Z.of_nat (length nexts)))
    nil
    (xizi_next_at head nexts)
    nexts.

Definition xizi_single_link_len_spec (head : Z) (nexts : list Z) : Z :=
  xizi_single_link_len_nat
    (Z.to_nat (Z.of_nat (length nexts)))
    (xizi_next_at head nexts)
    nexts.

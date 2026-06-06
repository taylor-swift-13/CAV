(* spec/85 *)
(* def add(lst):
"""Given a non-empty list of integers lst. add the even elements that are at odd indices..

Examples:
add([4, 2, 6, 7]) ==> 2
""" *)

Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sum_even_at_odd_indices (l : list Z) (n : nat) : Z :=
  match l with
  | nil => 0%Z
  | h :: t =>
      if andb (Nat.odd n) (Z.even h)
      then (h + sum_even_at_odd_indices t (S n))%Z
      else sum_even_at_odd_indices t (S n)
  end.

Definition add_impl (lst : list Z) : Z := sum_even_at_odd_indices lst 0.



Require Import Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Fixpoint sum_even_at_odd_upto_nat (n : nat) (l : list Z) : Z :=
  match n with
  | O => 0
  | S n' =>
      let s := sum_even_at_odd_upto_nat n' l in
      let i := Z.of_nat n' in
      let x := Znth (2 * i + 1) l 0 in
      if Z.eqb (Z.rem x 2) 0 then s + x else s
  end.

Definition sum_even_at_odd_upto (i : Z) (l : list Z) : Z :=
  sum_even_at_odd_upto_nat (Z.to_nat i) l.

Definition problem_85_pre (lst : list Z) : Prop :=
  (lst) <> []%list.

Definition problem_85_spec (lst : list Z) (output : Z) : Prop :=
  (output = add_impl lst).

Definition add_int_range (lst : list Z) : Prop :=
  forall i,
    0 <= i ->
    2 * i + 1 < Zlength lst ->
    INT_MIN <= sum_even_at_odd_upto i lst <= INT_MAX /\
    INT_MIN <= sum_even_at_odd_upto i lst + Znth (2 * i + 1) lst 0 <= INT_MAX.

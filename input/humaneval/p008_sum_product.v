(* spec/8 *)
(* """ For a given list of integers, return a tuple consisting of a sum and a product of all the integers in a list.
Empty sum should be equal to 0 and empty product should be equal to 1.
>>> sum_product([])
(0, 1)
>>> sum_product([1, 2, 3, 4])
(10, 24)
""" *)

(* *)

Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition list_int_range (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> INT_MIN <= Znth i l 0 <= INT_MAX.

Definition prefix_sum (l : list Z) (i : Z) : Z :=
  fold_left Z.add (sublist 0 i l) 0.

Definition prefix_product (l : list Z) (i : Z) : Z :=
  fold_left Z.mul (sublist 0 i l) 1.

Definition prefix_sum_product_int_range (l : list Z) (n : Z) : Prop :=
  forall i,
    0 <= i <= n ->
    INT_MIN <= prefix_sum l i <= INT_MAX /\
    INT_MIN <= prefix_product l i <= INT_MAX.

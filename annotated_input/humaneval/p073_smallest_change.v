(* spec/73 *)
(* def smallest_change(arr):
Given an array arr of integers, find the minimum number of elements that
need to be changed to make the array palindromic. A palindromic array is an array that
is read the same backwards and forwards. In one change, you can change one element to any other element.

For example:
smallest_change([1,2,3,5,4,7,9,6]) == 4
smallest_change([1, 2, 3, 4, 3, 2, 2]) == 1
smallest_change([1, 2, 3, 2, 1]) == 0*)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.

Import naive_C_Rules.
Local Open Scope Z_scope.

Definition problem_73_pre (arr : list Z) : Prop :=
  True.

Fixpoint count_half_mismatches_upto_nat (n : nat) (arr : list Z) : Z :=
  match n with
  | O => 0
  | S n' =>
      let i := Z.of_nat n' in
      count_half_mismatches_upto_nat n' arr +
      (if Z.eqb (Znth i arr 0) (Znth (Zlength arr - 1 - i) arr 0)
       then 0
       else 1)
  end.

Definition count_half_mismatches_upto (i : Z) (arr : list Z) : Z :=
  count_half_mismatches_upto_nat (Z.to_nat i) arr.

Definition problem_73_spec (arr : list Z) (out : Z) : Prop :=
  out = count_half_mismatches_upto (Zlength arr / 2) arr.

Definition smallest_change_int_range (arr : list Z) : Prop :=
  forall i,
    0 <= i ->
    2 * i < Zlength arr ->
    INT_MIN <= count_half_mismatches_upto i arr <= INT_MAX /\
    INT_MIN <= count_half_mismatches_upto i arr + 1 <= INT_MAX.


(* Ground-truth proof helpers. *)

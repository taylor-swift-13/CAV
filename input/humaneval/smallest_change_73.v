(* spec/73 *)
(* def smallest_change(arr):
Given an array arr of integers, find the minimum number of elements that
need to be changed to make the array palindromic. A palindromic array is an array that
is read the same backwards and forwards. In one change, you can change one element to any other element.

For example:
smallest_change([1,2,3,5,4,7,9,6]) == 4
smallest_change([1, 2, 3, 4, 3, 2, 2]) == 1
smallest_change([1, 2, 3, 2, 1]) == 0*)

Require Import List.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

(*
  count_diff l1 l2 acc := 计算 l1 和 l2 之间不同元素的数量
*)
Fixpoint count_diff (l1 l2: list Z) (acc: Z): Z :=
  match l1, l2 with
  | [], _ => acc
  | _, [] => acc
  | h1 :: t1, h2 :: t2 =>
    if Z.eqb h1 h2 then
      count_diff t1 t2 acc
    else
      count_diff t1 t2 (Z.succ acc)
  end.

Definition smallest_change_impl (arr: list Z): Z :=
  let len := length arr in
  let half_len := (len / 2)%nat in
  let first_half := firstn half_len arr in
  (* 使用 skipn 来获取列表的后半部分 *)
  let second_half := skipn (len - half_len) arr in
  count_diff first_half (rev second_half) 0.



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
  (out = smallest_change_impl arr).

Definition smallest_change_int_range (arr : list Z) : Prop :=
  forall i,
    0 <= i ->
    2 * i < Zlength arr ->
    INT_MIN <= count_half_mismatches_upto i arr <= INT_MAX /\
    INT_MIN <= count_half_mismatches_upto i arr + 1 <= INT_MAX.

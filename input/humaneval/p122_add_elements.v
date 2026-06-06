(* spec/122 *)
(* Given a non-empty array of integers arr and an integer k, return
the sum of the elements with at most two digits from the first k elements of arr.

Example:

Input: arr = [111,21,3,4000,5,6,7,8,9], k = 4
Output: 24 # sum of 21 + 3

Constraints:
1. 1 <= len(arr) <= 100
2. 1 <= k <= len(arr) *)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* 定义一个辅助函数来检查一个整数是否最多有两位数。
   这里我们使用 Z.ltb (less than boolean) 和 andb (boolean and)
   来确保返回类型是 bool。 *)
Definition is_at_most_two_digits (n : Z) : bool :=
  (Z.ltb (-100) n) && (Z.ltb n 100).

(* 1 <= length arr <= 100 且 1 <= k <= length arr *)

(* 定义程序规约 Spec *)

Require Import Coq.Bool.Bool.
Require Import Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Fixpoint sum_two_digit_upto_nat (n : nat) (l : list Z) : Z :=
  match n with
  | O => 0
  | S n' =>
      let s := sum_two_digit_upto_nat n' l in
      let i := Z.of_nat n' in
      let x := Znth i l 0 in
      if Z.leb (-99) x && Z.leb x 99 then s + x else s
  end.

Definition sum_two_digit_upto (i : Z) (l : list Z) : Z :=
  sum_two_digit_upto_nat (Z.to_nat i) l.

Definition problem_122_pre (arr : list Z) (k : Z) : Prop :=
  arr <> [] /\ 1 <= k <= Zlength arr.

Definition problem_122_spec (arr : list Z) (k result : Z) : Prop :=
  (let first_k_elements := sublist 0 k arr in
    let filtered_elements := filter is_at_most_two_digits first_k_elements in
    result = fold_left Z.add filtered_elements 0).

Definition sum_two_digit_int_range (k : Z) (arr : list Z) : Prop :=
  forall i,
    0 <= i ->
    i < k ->
    INT_MIN <= sum_two_digit_upto i arr <= INT_MAX /\
    INT_MIN <= sum_two_digit_upto i arr + Znth i arr 0 <= INT_MAX.

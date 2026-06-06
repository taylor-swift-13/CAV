(* spec/94 *)
(*def skjkasdkd(lst):
"""You are given a list of integers.
You need to find the largest prime value and return the sum of its digits.

Examples:
For lst = [0,3,2,1,3,5,7,4,5,5,5,2,181,32,4,32,3,2,32,324,4,3] the output should be 10
For lst = [1,0,1,8,2,4597,2,1,3,40,1,2,1,2,4,2,5,1] the output should be 25
For lst = [1,3,1,32,5107,34,83278,109,163,23,2323,32,30,1,9,3] the output should be 13
For lst = [0,724,32,71,99,32,6,0,5,91,83,0,5,6] the output should be 11
For lst = [0,81,12,3,1,21] the output should be 3
For lst = [0,8,1,2,1,7] the output should be 7
""" *)
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.Znumtheory.
Import ListNotations.
Open Scope nat_scope.
(*
  辅助定义2: 计算一个自然数各位数字之和 (使用燃料)
*)
Fixpoint sum_digits_fueled (n fuel : nat) : nat :=
  match fuel with
  | 0 => 0 (* 燃料耗尽，停止递归 *)
  | S fuel' =>
    match n with
    | 0 => 0 (* n 本身为 0，则各位和为 0 *)
    | _ => (n mod 10) + sum_digits_fueled (n / 10) fuel'
    end
  end.

Definition sum_digits (n : nat) : nat :=
  sum_digits_fueled n n.

(* 输入列表可含任意自然数（允许为空） *)


From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Coq.micromega.Lia.

Import naive_C_Rules.
Open Scope Z_scope.

Definition problem_94_pre (lst : list Z) : Prop :=
  True.

Definition list_nonneg_int_range (lst : list Z) : Prop :=
  forall i,
    0 <= i < Zlength lst ->
    0 <= Znth i lst 0 <= INT_MAX.

Definition largest_prime_prefix (i : Z) (lst : list Z) (largest : Z) : Prop :=
  0 <= i <= Zlength lst /\
  0 <= largest <= INT_MAX /\
  ((largest = 0 /\
    forall k, 0 <= k < i -> ~ prime (Znth k lst 0)) \/
   (prime largest /\
    (exists k, 0 <= k < i /\ largest = Znth k lst 0) /\
    forall k, 0 <= k < i -> prime (Znth k lst 0) -> Znth k lst 0 <= largest)).

Definition prime_scan_state (x j prime : Z) : Prop :=
  1 < x <= INT_MAX /\
  2 <= j <= x + 1 /\
  0 <= prime <= 1 /\
  (prime <> 0 ->
   forall d, 2 <= d < j -> x mod d <> 0) /\
  (prime = 0 ->
   exists d, 2 <= d < j /\ d < x /\ x mod d = 0).

Definition digit_sum_int_range (n : Z) : Prop :=
  0 <= n <= INT_MAX.

Fixpoint sum_digits_fuel (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel0 =>
      if Z.leb n 0 then 0 else (n mod 10) + sum_digits_fuel (n / 10) fuel0
  end.

Definition digit_sum_state (original current sum : Z) : Prop :=
  0 <= original <= INT_MAX /\
  exists fuel : nat,
    0 <= current /\
    0 <= sum /\
    current < 10 ^ (Z.of_nat fuel) /\
    sum + sum_digits_fuel current fuel <= 100 /\
    sum + Z.of_nat (sum_digits (Z.to_nat current)) =
      Z.of_nat (sum_digits (Z.to_nat original)).

Definition problem_94_spec (lst : list Z) (out : Z) : Prop :=
  (exists p,
      In p lst /\
      prime p /\
      (forall p', In p' lst -> prime p' -> p' <= p) /\
      out = Z.of_nat (sum_digits (Z.to_nat p)))
    \/
    ((forall x, In x lst -> ~ prime x) /\ out = 0).

(* spec/96 *)
(* def count_up_to(n):
"""Implement a function that takes an non-negative integer and returns an array of the first n
integers that are prime numbers and less than n.
for example:
count_up_to(5) => [2,3]
count_up_to(11) => [2,3,5,7]
count_up_to(0) => []
count_up_to(20) => [2,3,5,7,11,13,17,19]
count_up_to(1) => []
count_up_to(18) => [2,3,5,7,11,13,17]
""" *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Sorting.Sorted. (* 引入 Sorted 定义 *)
Import ListNotations.
Open Scope nat_scope.

(* n 是自然数即非负，无附加约束 *)


Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Close Scope nat_scope.
Open Scope Z_scope.

Definition problem_96_pre (n : Z) : Prop :=
  True.

Definition problem_96_spec (n : Z) (result : list Z) : Prop :=
  0 <= n /\
  (forall p, In p result -> 2 <= p < n /\ prime p) /\
  (forall p, 2 <= p < n -> prime p -> In p result) /\
  Sorted Z.lt result /\
  NoDup result.

Definition count_up_to_state (i : Z) (result : list Z) : Prop :=
  2 <= i /\
  Zlength result <= i /\
  (forall p, In p result -> 2 <= p < i /\ prime p) /\
  (forall p, 2 <= p < i -> prime p -> In p result) /\
  Sorted Z.lt result /\
  NoDup result.

Definition prime_test_state (candidate : Z) (result : list Z) (j isp : Z) : Prop :=
  0 <= j <= Zlength result /\
  0 <= isp <= 1 /\
  (isp <> 0 ->
   forall k,
     0 <= k < j ->
     Znth k result 0 <= candidate / Znth k result 0 ->
     candidate mod Znth k result 0 <> 0) /\
  (isp = 0 ->
   exists k,
     0 <= k < j /\
     Znth k result 0 <= candidate / Znth k result 0 /\
     candidate mod Znth k result 0 = 0).

Local Open Scope Z_scope.

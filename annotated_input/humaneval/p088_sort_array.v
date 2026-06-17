(* spec/88 *)
(* def sort_array(array):
"""
Given an array of non-negative integers, return a copy of the given array after sorting,
you will sort the given array in ascending order if the sum( first index value, last index value) is odd,
or sort it in descending order if the sum( first index value, last index value) is even.

Note:
* don't change the given array.

Examples:
* sort_array([]) => []
* sort_array([5]) => [5]
* sort_array([2, 4, 3, 0, 1, 5]) => [0, 1, 2, 3, 4, 5]
* sort_array([2, 4, 3, 0, 1, 5, 6]) => [6, 5, 4, 3, 2, 1, 0]
""" *)
Require Import List.
Require Import Arith.
Require Import Permutation.
Require Import Coq.Sorting.Sorted.
Import ListNotations.


(* sort_array 函数的程序规约 *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import naive_C_Rules.
Local Open Scope Z_scope.

Definition problem_88_pre (input : list Z) : Prop :=
  True.

Definition sort_array_input_range (input : list Z) : Prop :=
  (forall i, 0 <= i < Zlength input -> 0 <= Znth i input 0 <= INT_MAX) /\
  (0 < Zlength input ->
   Znth 0 input 0 + Znth (Zlength input - 1) input 0 <= INT_MAX).

Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
  if Z.eqb ascending 0 then Sorted Z.ge l else Sorted Z.le l.

Definition problem_88_spec (input output : list Z) : Prop :=
  (* 输出必须是输入的排列 *)
  Permutation input output /\
  match input with
    | [] => output = []
    | [x] => output = [x]
    | h :: _ =>
      (* 安全地获取最后一个元素 *)
      let last_elem := last input h in
      if Z.eqb ((h + last_elem) mod 2) 1 then
        Sorted Z.le output
      else
        Sorted Z.ge output
    end.

Fixpoint copy_prefix_nat (n : nat) (input : list Z) : list Z :=
  match n with
  | O => []
  | S n' => copy_prefix_nat n' input ++ [Znth (Z.of_nat n') input 0]
  end.

Definition copy_prefix (n : Z) (input : list Z) : list Z :=
  copy_prefix_nat (Z.to_nat n) input.

Definition reverse_step (size i : Z) (l : list Z) : list Z :=
  replace_Znth (size - 1 - i) (Znth i l 0)
    (replace_Znth i (Znth (size - 1 - i) l 0) l).

Fixpoint reverse_loop_nat (size : Z) (n : nat) (l : list Z) : list Z :=
  match n with
  | O => l
  | S n' => reverse_step size (Z.of_nat n') (reverse_loop_nat size n' l)
  end.

Definition reverse_loop (size i : Z) (l : list Z) : list Z :=
  reverse_loop_nat size (Z.to_nat i) l.

(* spec/116 *)
(*In this Kata, you have to sort an array of non-negative integers according to
number of ones in their binary representation in ascending order.
For similar number of ones, sort based on decimal value.

It must be implemented like this:
>>> sort_array([1, 5, 2, 3, 4]) == [1, 2, 3, 4, 5]
>>> sort_array([1, 0, 2, 3, 4]) [0, 1, 2, 3, 4] *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Permutation.
Require Import Sorting.Sorted.
Import ListNotations.

(*
  定义一个带有 "燃料" 参数的辅助函数。
  递归在燃料参数 `fuel` 上是结构性的 (S fuel' -> fuel')，
  这满足了 Coq 对 Fixpoint 的要求。
*)
Fixpoint count_ones_helper (n fuel : nat) : nat :=
  match fuel with
  | 0 => 0 (* 燃料耗尽，停止递归 *)
  | S fuel' => (* 还有燃料 *)
      match n with
      | 0 => 0 (* n为0，递归的自然基准情况 *)
      | _ => (n mod 2) + count_ones_helper (n / 2) fuel' (* 递归调用，燃料减少 *)
      end
  end.

(*
  定义主函数，它用 n 自身作为初始燃料来调用辅助函数。
  对于任何 n，其二进制表示的位数都小于 n 本身，所以 n 是足够多的“燃料”。
*)
Definition count_ones (n : nat) : nat :=
  count_ones_helper n 31.

(*
  定义两个自然数的比较逻辑:
  - 首先比较它们二进制中1的个数
  - 如果1的个数相等，则直接比较数值大小
*)
Definition lt_custom (a b : nat) : Prop :=
  let ones_a := count_ones a in
  let ones_b := count_ones b in
  (ones_a < ones_b) \/ (ones_a = ones_b /\ a < b).

(* 用于实现的bool版本比较函数 *)
Definition lt_custom_bool (a b : nat) : bool :=
  let ones_a := count_ones a in
  let ones_b := count_ones b in
  if ones_a <? ones_b then true
  else if ones_a =? ones_b then a <? b
  else false.

(*
  排序函数的规约 (Spec)

  它描述了输入列表(input)和输出列表(output)之间的关系
*)

Definition should_swap_custom_bool (a b : nat) : bool :=
  if count_ones b <? count_ones a then true
  else if count_ones b =? count_ones a then b <? a
  else false.

Definition swap_adjacent_custom (j : nat) (l : list nat) : list nat :=
  match nth_error l j, nth_error l (S j) with
  | Some a, Some b =>
      if should_swap_custom_bool a b
      then firstn j l ++ b :: a :: skipn (S (S j)) l
      else l
  | _, _ => l
  end.

Fixpoint bubble_pass_custom_from (fuel j : nat) (l : list nat) : list nat :=
  match fuel with
  | O => l
  | S fuel' => bubble_pass_custom_from fuel' (S j) (swap_adjacent_custom j l)
  end.

Definition bubble_pass_custom (l : list nat) : list nat :=
  bubble_pass_custom_from (length l - 1)%nat 0 l.

Fixpoint bubble_sort_custom_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | O => l
  | S fuel' => bubble_sort_custom_fuel fuel' (bubble_pass_custom l)
  end.

Definition sort_array_impl (input : list nat) : list nat :=
  bubble_sort_custom_fuel (length input) input.

(* 输入为非负整数列表（nat 已保证） *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition Zabs (x : Z) : Z := Z.abs x.

Definition bit_fuel_116 : nat := 31%nat.

Fixpoint bit_count_loop_116 (fuel : nat) (n acc : Z) : Z :=
  match fuel with
  | O => acc
  | S fuel' =>
      if Z.leb n 0
      then acc
      else bit_count_loop_116 fuel' (n ÷ 2) (acc + Z.rem n 2)
  end.

Definition bit_count_116 (x : Z) : Z :=
  bit_count_loop_116 bit_fuel_116 x 0.

Definition sort_array_116_int_range (input : list Z) : Prop :=
  forall i, 0 <= i < Zlength input -> 0 <= Znth i input 0 < INT_MAX.

Definition bit_count_state_116 (x n b : Z) : Prop :=
  0 <= x < INT_MAX /\
  0 <= n < INT_MAX /\
  0 <= b <= 31 /\
  exists fuel,
    n < 2 ^ Z.of_nat fuel /\
    bit_count_loop_116 fuel n b = bit_count_116 x.

Definition bit_count_state_at_116 (i : Z) (input : list Z) (n b : Z) : Prop :=
  bit_count_state_116 (Znth i input 0) n b.

Definition bit_count_result_116 (x r : Z) : Prop :=
  0 <= x < INT_MAX /\
  0 <= r <= 31 /\
  r = bit_count_116 x.

Definition should_swap_116 (a b : Z) : bool :=
  if bit_count_116 b <? bit_count_116 a then true
  else if bit_count_116 b =? bit_count_116 a then b <? a
  else false.

Definition swap_adjacent_116 (j : nat) (l : list Z) : list Z :=
  match nth_error l j, nth_error l (S j) with
  | Some a, Some b =>
      if should_swap_116 a b
      then firstn j l ++ b :: a :: skipn (S (S j)) l
      else l
  | _, _ => l
  end.

Fixpoint bubble_pass_116_from (fuel j : nat) (l : list Z) : list Z :=
  match fuel with
  | O => l
  | S fuel' => bubble_pass_116_from fuel' (S j) (swap_adjacent_116 j l)
  end.

Definition bubble_pass_116 (l : list Z) : list Z :=
  bubble_pass_116_from (length l - 1)%nat 0 l.

Fixpoint bubble_sort_116_fuel (fuel : nat) (l : list Z) : list Z :=
  match fuel with
  | O => l
  | S fuel' => bubble_sort_116_fuel fuel' (bubble_pass_116 l)
  end.

Definition bubble_sort_116 (l : list Z) : list Z :=
  bubble_sort_116_fuel (length l) l.

Definition problem_116_pre (input : list Z) : Prop :=
  True.

Definition problem_116_spec (input output : list Z) : Prop :=
  output = bubble_sort_116 input.

Definition sort_copy_prefix_116
  (i : Z) (input output : list Z) : Prop :=
  0 <= i <= Zlength input /\
  Zlength output = i /\
  output = sublist 0 i input.

Definition sort_score_prefix_116
  (i : Z) (input scores : list Z) : Prop :=
  0 <= i <= Zlength input /\
  Zlength scores = i /\
  scores = map bit_count_116 (sublist 0 i input).

Definition bubble_outer_prefix_116 (i : Z) (input : list Z) : list Z :=
  bubble_sort_116_fuel (Z.to_nat i) input.

Definition bubble_inner_prefix_116 (i j : Z) (input : list Z) : list Z :=
  bubble_pass_116_from (Z.to_nat (j - 1)) 0%nat (bubble_outer_prefix_116 i input).

Definition sort_outer_state_116
  (i : Z) (input output scores : list Z) : Prop :=
  0 <= i <= Zlength input /\
  Zlength output = Zlength input /\
  Zlength scores = Zlength input /\
  output = bubble_outer_prefix_116 i input /\
  scores = map bit_count_116 output.

Definition sort_inner_state_116
  (i j : Z) (input output scores : list Z) : Prop :=
  0 <= i < Zlength input /\
  1 <= j <= Zlength input /\
  Zlength output = Zlength input /\
  Zlength scores = Zlength input /\
  output = bubble_inner_prefix_116 i j input /\
  scores = map bit_count_116 output.

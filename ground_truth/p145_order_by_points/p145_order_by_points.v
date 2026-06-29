(* spec/145 *)
(* def order_by_points(nums):
"""
Write a function which sorts the given list of integers
in ascending order according to the sum of their digits.
Note: if there are several items with similar sum of their digits,
order them based on their index in original list.

For example:
>>> order_by_points([1, 11, -1, -11, -12]) == [-1, -11, 1, -12, 11]
>>> order_by_points([]) == []
""" *)

Require Import ZArith.
Require Import Coq.Lists.List.
Require Import Permutation.
Require Import Sorting.Sorted.
Require Import Arith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sum_digits_pos_fuel (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => 0
  | S f => if Z_le_gt_dec n 0 then 0 else (n mod 10) + sum_digits_pos_fuel f (n / 10)
  end.

Fixpoint msd_fuel (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n mod 10
  | S f => if Z_lt_le_dec n 10 then n else msd_fuel f (n / 10)
  end.

Definition digit_fuel_145 : nat := 8%nat.

Fixpoint highest_power10_loop_145 (fuel : nat) (t p : Z) : Z :=
  match fuel with
  | O => p
  | S fuel' =>
      if Z.leb (p * 10) t
      then highest_power10_loop_145 fuel' t (p * 10)
      else p
  end.

Fixpoint digit_tail_loop_145 (fuel : nat) (t sum : Z) : Z :=
  match fuel with
  | O => sum
  | S fuel' =>
      if Z.leb t 0
      then sum
      else digit_tail_loop_145 fuel' (t / 10) (sum + t mod 10)
  end.

Definition sum_digits (n : Z) : Z :=
  let t := Z.abs n in
  let msd := msd_fuel digit_fuel_145 t in
  let sum := if Z_ge_dec n 0 then msd else - msd in
  if Z.leb 10 t
  then digit_tail_loop_145
         digit_fuel_145
         (t mod highest_power10_loop_145 digit_fuel_145 t 1)
         sum
  else sum.

Definition le_stable (p1 p2 : Z * nat) : Prop :=
  let (z1, i1) := p1 in
  let (z2, i2) := p2 in
  let s1 := sum_digits z1 in
  let s2 := sum_digits z2 in
  s1 < s2 \/ (s1 = s2 /\ (i1 <= i2)%nat).

Definition swap_adjacent_points (j : nat) (l : list Z) : list Z :=
  match nth_error l j, nth_error l (S j) with
  | Some a, Some b =>
      if Z.gtb (sum_digits a) (sum_digits b)
      then firstn j l ++ b :: a :: skipn (S (S j)) l
      else l
  | _, _ => l
  end.

Fixpoint bubble_pass_points_from (fuel j : nat) (l : list Z) : list Z :=
  match fuel with
  | O => l
  | S fuel' => bubble_pass_points_from fuel' (S j) (swap_adjacent_points j l)
  end.

Definition bubble_pass_points (l : list Z) : list Z :=
  bubble_pass_points_from (length l - 1)%nat 0 l.

Fixpoint bubble_sort_points_fuel (fuel : nat) (l : list Z) : list Z :=
  match fuel with
  | O => l
  | S fuel' => bubble_sort_points_fuel fuel' (bubble_pass_points l)
  end.

Definition bubble_sort_points (l : list Z) : list Z :=
  bubble_sort_points_fuel (length l) l.

Fixpoint insert_sorted (x : Z * nat) (l : list (Z * nat)) : list (Z * nat) :=
  match l with
  | [] => [x]
  | h :: t => let '(zx, ix) := x in let '(zh, ih) := h in
              let sx := sum_digits zx in let sh := sum_digits zh in
              if Z.ltb sx sh then x :: l
              else if Z.eqb sx sh then if Nat.leb ix ih then x :: l else h :: insert_sorted x t
              else h :: insert_sorted x t
  end.

Fixpoint stable_sort (l : list (Z * nat)) : list (Z * nat) :=
  match l with [] => [] | h :: t => insert_sorted h (stable_sort t) end.

Definition order_by_points_impl (l_in : list Z) : list Z :=
  bubble_sort_points l_in.

(* 任意整数列表输入均可 *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition Zabs (x : Z) : Z := Z.abs x.

Definition first_digit_value_145 (n : Z) : Z :=
  msd_fuel digit_fuel_145 n.

Definition first_digit_state_145 (original current : Z) : Prop :=
  exists fuel,
    0 <= current <= original /\
    current < 10 ^ Z.of_nat fuel /\
    first_digit_value_145 original = msd_fuel fuel current.

Fixpoint signed_digit_tail_loop (fuel : nat) (t sum : Z) : Z :=
  match fuel with
  | O => sum
  | S fuel' =>
      if Z.leb t 0
      then sum
      else signed_digit_tail_loop fuel' (t / 10) (sum + t mod 10)
  end.

Definition signed_digit_tail_state (x t sum : Z) : Prop :=
  0 <= t < 100000000 /\
  -100 <= sum /\
  exists fuel,
    t < 10 ^ Z.of_nat fuel /\
    0 <= sum_digits_pos_fuel fuel t /\
    sum + sum_digits_pos_fuel fuel t <= 100 /\
    signed_digit_tail_loop fuel t sum = sum_digits x.

Definition highest_power10_state (x t p sum : Z) : Prop :=
  t = Z.abs x /\
  10 <= t < 100000000 /\
  1 <= p <= t /\
  -100 <= sum <= 100 /\
  exists fuel,
    (highest_power10_loop_145 fuel t p) * 10 > t /\
    signed_digit_tail_state x (Z.rem t (highest_power10_loop_145 fuel t p)) sum.

Definition signed_digit_score_result (x r : Z) : Prop :=
  INT_MIN < x < INT_MAX /\
  Z.abs x < 100000000 /\
  INT_MIN < r < INT_MAX /\
  r = sum_digits x.

Definition order_by_points_int_range (nums : list Z) : Prop :=
  forall i, 0 <= i < Zlength nums ->
    INT_MIN < Znth i nums 0 < INT_MAX /\
    Z.abs (Znth i nums 0) < 100000000.

Definition problem_145_pre (nums : list Z) : Prop :=
  True.

Definition problem_145_spec (nums output : list Z) : Prop :=
  output = order_by_points_impl nums.

Definition order_copy_prefix
  (i : Z) (input output scores : list Z) : Prop :=
  0 <= i <= Zlength input /\
  Zlength output = i /\
  Zlength scores = i /\
  output = sublist 0 i input /\
  scores = map sum_digits output.

Definition bubble_outer_prefix_145 (i : Z) (input : list Z) : list Z :=
  bubble_sort_points_fuel (Z.to_nat i) input.

Definition bubble_inner_prefix_145 (i j : Z) (input : list Z) : list Z :=
  bubble_pass_points_from (Z.to_nat (j - 1)) 0%nat (bubble_outer_prefix_145 i input).

Definition order_sort_outer_state
  (i : Z) (input output scores : list Z) : Prop :=
  0 <= i <= Zlength input /\
  Zlength output = Zlength input /\
  Zlength scores = Zlength input /\
  output = bubble_outer_prefix_145 i input /\
  scores = map sum_digits output.

Definition order_sort_inner_state
  (i j : Z) (input output scores : list Z) : Prop :=
  0 <= i < Zlength input /\
  1 <= j <= Zlength input /\
  Zlength output = Zlength input /\
  Zlength scores = Zlength input /\
  output = bubble_inner_prefix_145 i j input /\
  scores = map sum_digits output.

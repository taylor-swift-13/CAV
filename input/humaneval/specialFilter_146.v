(* spec/146 *)
(* def specialFilter(nums):
"""Write a function that takes an array of numbers as input and returns
the number of elements in the array that are greater than 10 and both
first and last digits of a number are odd (1, 3, 5, 7, 9).
For example:
specialFilter([15, -73, 14, -15]) => 1
specialFilter([33, -2, -3, 45, 21, 109]) => 2
""" *)

Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Strings.Ascii.
Import ListNotations.
Open Scope Z_scope.

Definition last_digit (n : Z) : Z := Z.abs (n mod 10).

Fixpoint msd_fuel (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n mod 10
  | S f => if Z_lt_dec n 10 then n else msd_fuel f (n/10)
  end.

Definition special_number_b (n : Z) : bool :=
  let abs_n := Z.abs n in (10 <? n) && (Z.odd (msd_fuel (Z.to_nat abs_n) abs_n)) && (Z.odd (last_digit abs_n)).

Definition specialFilter_impl (nums : list Z) : Z := Z.of_nat (length (filter special_number_b nums)).

(* 任意整数列表输入均可 *)


Require Import Coq.ZArith.Zquot.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition problem_146_pre (nums : list Z) : Prop :=
  True.

Definition problem_146_spec (nums : list Z) (output : Z) : Prop :=
  (output = specialFilter_impl nums).

Definition first_digit_value (n : Z) : Z :=
  msd_fuel (Z.to_nat n) n.

Definition first_digit_state (original current : Z) : Prop :=
  exists fuel,
    0 <= current <= original /\
    current < 10 ^ Z.of_nat fuel /\
    first_digit_value original = msd_fuel fuel current.

Definition special_number_c (n : Z) : Prop :=
  special_number_b n = true.

Definition not_special_number_c (n : Z) : Prop :=
  special_number_b n = false.

Definition special_filter_prefix (i : Z) (nums : list Z) (count : Z) : Prop :=
  0 <= i <= Zlength nums /\
  count = Z.of_nat (length (filter special_number_b (sublist 0 i nums))).

Definition special_scalar_int_range (x : Z) : Prop :=
  INT_MIN <= x <= INT_MAX.

Definition special_filter_int_range (nums : list Z) : Prop :=
  forall i, 0 <= i < Zlength nums -> special_scalar_int_range (Znth i nums 0).

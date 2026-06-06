(* spec/108 *)
(* Write a function count_nums which takes an array of integers and returns
the number of elements which has a sum of digits > 0.
If a number is negative, then its first signed digit will be negative:
e.g. -123 has signed digits -1, 2, and 3.
>>> count_nums([]) == 0
>>> count_nums([-1, 11, -11]) == 1
>>> count_nums([1, 1, 2]) == 3 *)

Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint signed_digit_loop (fuel : nat) (w sum : Z) : Z :=
  match fuel with
  | O => sum - w
  | S fuel' =>
      if w <? 10 then sum - w
      else signed_digit_loop fuel' (w / 10) (sum + w mod 10)
  end.

Definition sum_digits (z : Z) : Z :=
  if z >? 0 then 1
  else signed_digit_loop 11 (Z.abs z) 0.

Definition count_nums_impl (l : list Z) : Z :=
  Z.of_nat (length (filter (fun z => Z.gtb (sum_digits z) 0) l)).

(* 输入列表可为任意整数列表 *)


From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Coq.micromega.Lia.

Import naive_C_Rules.

Definition problem_108_pre (l : list Z) : Prop :=
  True.

Definition count_nums_int_range (l : list Z) : Prop :=
  forall i,
    0 <= i < Zlength l ->
    INT_MIN < Znth i l 0 <= INT_MAX.

Definition count_nums_prefix (i : Z) (l : list Z) (num : Z) : Prop :=
  0 <= i <= Zlength l /\
  num = count_nums_impl (sublist 0 i l).

Definition digit_scan_state (original current sum : Z) : Prop :=
  0 <= original <= INT_MAX /\
  exists fuel : nat,
    0 <= current <= original /\
    current < 10 ^ Z.of_nat fuel /\
    0 <= sum /\
    sum + current <= INT_MAX /\
    signed_digit_loop fuel current sum = signed_digit_loop 11 original 0.

Definition problem_108_spec (l : list Z) (out : Z) : Prop :=
  out = count_nums_impl l.

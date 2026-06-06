(* spec/9 *)
(* """ From a given list of integers, generate a list of rolling maximum element found until given moment
in the sequence.
>>> rolling_max([1, 2, 3, 2, 3, 4, 2])
[1, 2, 3, 3, 3, 4, 4]
""" *)

(* Spec(input, output) :=

length(output) == length(input) ∧

∀i. 0 ≤ i < length(output) ∧
        (∀j. 0 ≤ j ≤ i → input[j] ≤ output[i]) ∧
        (∃j. 0 ≤ j ≤ i ∧ input[j] = output[i]) *)

Require Import List ZArith.
From AUXLib Require Import ListLib.
Import ListNotations.
Open Scope Z_scope.

Definition problem_9_pre : Prop := True.

Definition problem_9_spec (input output : list Z) :=
  Zlength output = Zlength input /\
  forall i,
    0 <= i < Zlength output ->
    (forall j, 0 <= j <= i -> Znth j input 0 <= Znth i output 0) /\
    (exists j, 0 <= j <= i /\ Znth j input 0 = Znth i output 0).

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition list_int_range (l : list Z) : Prop :=
  forall i, (i < length l)%nat -> INT_MIN <= nth i l 0 <= INT_MAX.

Fixpoint running_max_val (mx : Z) (l : list Z) : Z :=
  match l with
  | [] => mx
  | x :: xs => running_max_val (Z.max mx x) xs
  end.

Fixpoint rolling_max_f (mx : Z) (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
      let m := Z.max mx x in
      m :: rolling_max_f m xs
  end.

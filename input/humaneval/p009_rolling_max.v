Require Import Coq.Lists.List Coq.ZArith.ZArith Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_9_pre : Prop := True.

Definition prefix_max_at (input : list Z) (i m : Z) : Prop :=
  (forall j, 0 <= j <= i -> Znth j input 0 <= m) /\
  (exists j, 0 <= j <= i /\ Znth j input 0 = m).

Definition problem_9_spec (input output : list Z) : Prop :=
  Zlength output = Zlength input /\
  forall i,
    0 <= i < Zlength output ->
    prefix_max_at input i (Znth i output 0).

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

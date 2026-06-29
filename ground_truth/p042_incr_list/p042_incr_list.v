(* spec/42 *)
(* Return list with elements incremented by 1.
>>> incr_list([1, 2, 3])
[2, 3, 4]
>>> incr_list([5, 3, 5, 2, 3, 3, 9, 0, 123])
[6, 4, 6, 3, 4, 4, 10, 1, 124] *)

(* Spec(input : list int, output : list int) :=
​	length(input) = length(output) /\
​	∀i ∈ [0, length(input)), outpu[i] = input[i] + 1
*)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From AUXLib Require Import ListLib.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `incr_list` *)
Definition problem_42_pre (input : list Z) : Prop := True.

Definition problem_42_spec(input output : list Z) : Prop :=
  Zlength input = Zlength output /\
  forall i, 0 <= i < Zlength output -> Znth i output 0 = Znth i input 0 + 1.

Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition map_incr (l : list Z) : list Z :=
  map (fun x => x + 1) l.

Definition list_incr_int_range (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> INT_MIN <= Znth i l 0 + 1 <= INT_MAX.

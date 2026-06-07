(* spec/23 *)
(* """ Return length of given string
>>> strlen('')
0
>>> strlen('abc')
3
""" *)

(* ​	Spec(input : string, output : int) :=

​		output = length(input) *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
From AUXLib Require Import ListLib.
Import ListNotations.

Local Open Scope Z_scope.

Definition problem_23_pre (input : list Z) : Prop :=
  forall k, 0 <= k < Zlength input -> Znth k input 0 <> 0.

Definition problem_23_spec (input : list Z) (output : Z) : Prop :=
  output = Zlength input.

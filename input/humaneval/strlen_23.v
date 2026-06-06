(* spec/23 *)
(* """ Return length of given string
>>> strlen('')
0
>>> strlen('abc')
3
""" *)

(* ​	Spec(input : string, output : int) :=

​		output = length(input) *)
Require Import String.

(* Pre: no additional constraints for `strlen` by default *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition problem_23_pre (input : list Z) : Prop :=
  True.

Definition problem_23_spec (input : list Z) (output : Z) : Prop :=
  output = Z.of_nat (String.length (string_of_list input)).

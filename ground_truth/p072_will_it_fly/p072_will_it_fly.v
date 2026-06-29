(* spec/72 *)
(* def will_it_fly(q,w):
'''
Write a function that returns True if the object q will fly, and False otherwise.
The object q will fly if it's balanced (it is a palindromic list) and the sum of its elements is less than or equal the maximum possible weight w.

Example:
will_it_fly([1, 2], 5) ➞ False
# 1+2 is less than the maximum possible weight, but it's unbalanced.

will_it_fly([3, 2, 3], 1) ➞ False
# it's balanced, but 3+2+3 is more than the maximum possible weight.

will_it_fly([3, 2, 3], 9) ➞ True
# 3+2+3 is less than the maximum possible weight, and it's balanced.

will_it_fly([3], 5) ➞ True
# 3 is less than the maximum possible weight, and it's balanced.
'''*)
Require Import List.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.


(* will_it_fly 函数的程序规约*)

From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.

Import naive_C_Rules.
Local Open Scope Z_scope.

Definition problem_72_pre (q : list Z) (w : Z) : Prop :=
  True.

Definition mirror_all (q : list Z) : Prop :=
  forall k,
    0 <= k < Zlength q ->
    Znth k q 0 = Znth (Zlength q - 1 - k) q 0.

Definition problem_72_spec (q : list Z) (w out : Z) : Prop :=
  (out = 0 \/ out = 1) /\
    ((((Z.eqb out 1)) = true <-> (q = rev q) /\ (fold_left (fun acc x => acc + x) q 0 <= w))).

Definition will_it_fly_int_range (q : list Z) : Prop :=
  forall i,
    0 <= i <= Zlength q ->
    INT_MIN <= sum (sublist 0 i q) <= INT_MAX.


(* Ground-truth proof helpers. *)

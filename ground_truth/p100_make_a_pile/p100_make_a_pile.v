(* spec/100 *)
(* Given a positive integer n, you have to make a pile of n levels of stones.
The first level has n stones.
The number of stones in the next level is:
- the next odd number if n is odd.
- the next even number if n is even.
Return the number of stones in each level in a list, where element at index
i represents the number of stones in the level (i+1).

Examples:
>>> make_a_pile(3)
[3, 5, 7] *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* n 必须是正整数 *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition problem_100_pre (n : Z) : Prop :=
  n > 0.

Definition problem_100_spec (n : Z) (out : list Z) : Prop :=
  n > 0 /\
  Zlength out = n /\
  forall i, 0 <= i < n -> Znth i out 0 = n + 2 * i.

Definition pile_int_range (n : Z) : Prop :=
  forall i, 0 <= i < n -> INT_MIN <= n + 2 * i <= INT_MAX.

Definition make_pile (n : Z) : list Z :=
  map (fun i => n + 2 * i) (Zseq 0 (Z.to_nat n)).

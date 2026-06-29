(* spec/135 *)
(* def can_arrange(arr):
Create a function which returns the largest index of an element which
is not greater than or equal to the element immediately preceding it. If
no such element exists then return -1. The given array will not contain
duplicate values.

Examples:
can_arrange([1,2,4,3,5]) = 3
can_arrange([1,2,3]) = -1 *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Import ListNotations.

Open Scope Z_scope.

Definition can_arrange_hit (l : list Z) (i : Z) : Prop :=
  0 <= i < Zlength l /\ Znth i l 0 <= i.

Definition can_arrange_prefix (i : Z) (l : list Z) (max : Z) : Prop :=
  0 <= i <= Zlength l /\
  -1 <= max < i /\
  (max = -1 \/ can_arrange_hit l max) /\
  (forall j, 0 <= j < i -> can_arrange_hit l j -> j <= max).

Definition problem_135_pre (l : list Z) : Prop :=
  NoDup (l).

Definition problem_135_spec (l : list Z) (r : Z) : Prop :=
  ((r = -1 /\ forall k, ~ can_arrange_hit l k)
    \/
    (exists k : Z,
        r = k /\
        can_arrange_hit l k /\
        (forall j : Z, can_arrange_hit l j -> j <= k))).

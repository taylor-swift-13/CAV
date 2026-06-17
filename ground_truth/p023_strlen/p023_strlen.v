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

Lemma p023_nonzero_index_lt : forall l n i,
  Zlength l = n ->
  (forall k, 0 <= k /\ k < n -> Znth k l 0 <> 0) ->
  0 <= i ->
  i <= n ->
  Znth i (app l (cons 0 nil)) 0 <> 0 ->
  i < n.
Proof.
  intros l n i Hlen Hnz Hi Hle Hchar.
  rewrite <- Hlen in *.
  destruct (Z_lt_ge_dec i (Zlength l)) as [Hlt | Hge]; [exact Hlt |].
  assert (i = Zlength l) by lia.
  subst i.
  rewrite app_Znth2 in Hchar by lia.
  replace (Zlength l - Zlength l) with 0 in Hchar by lia.
  simpl in Hchar.
  contradiction.
Qed.

Lemma p023_zero_index_eq : forall l n i,
  Zlength l = n ->
  (forall k, 0 <= k /\ k < n -> Znth k l 0 <> 0) ->
  0 <= i ->
  i <= n ->
  Znth i (app l (cons 0 nil)) 0 = 0 ->
  i = n.
Proof.
  intros l n i Hlen Hnz Hi Hle Hchar.
  rewrite <- Hlen in *.
  destruct (Z_lt_ge_dec i (Zlength l)) as [Hlt | Hge].
  - rewrite app_Znth1 in Hchar by lia.
    specialize (Hnz i ltac:(lia)).
    contradiction.
  - lia.
Qed.

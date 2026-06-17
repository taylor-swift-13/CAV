(* spec/52 *)
(* def below_threshold(l: list, t: int):
"""Return True if all numbers in the list l are below threshold t.
>>> below_threshold([1, 2, 4, 10], 100)
True
>>> below_threshold([1, 20, 4, 10], 5)
False
""" *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

(* index-based (verification-friendly): all elements < t, by Znth over [0, Zlength) *)
Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall i, 0 <= i < Zlength l -> Znth i l 0 < t) <-> (output = true).

Lemma problem_52_spec_false_of_counter : forall l n t i,
  Zlength l = n ->
  0 <= i < n ->
  Znth i l 0 >= t ->
  problem_52_spec l t false.
Proof.
  intros l n t i Hlen Hi Hge.
  unfold problem_52_spec.
  split; intro H.
  - specialize (H i).
    assert (0 <= i < Zlength l) by lia.
    specialize (H H0).
    lia.
  - discriminate H.
Qed.

Lemma problem_52_spec_true_of_all_below : forall l n t,
  Zlength l = n ->
  (forall k, 0 <= k < n -> Znth k l 0 < t) ->
  problem_52_spec l t true.
Proof.
  intros l n t Hlen Hall.
  unfold problem_52_spec.
  split.
  - intros _. reflexivity.
  - intros _ k Hk.
    apply Hall.
    lia.
Qed.

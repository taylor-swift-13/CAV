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

Lemma can_arrange_prefix_init : forall l,
  0 <= Zlength l ->
  can_arrange_prefix 0 l (-1).
Proof.
  intros l Hlen.
  unfold can_arrange_prefix.
  repeat split; try lia.
Qed.

Lemma can_arrange_prefix_keep : forall i l max,
  can_arrange_prefix i l max ->
  0 <= i < Zlength l ->
  ~ can_arrange_hit l i ->
  can_arrange_prefix (i + 1) l max.
Proof.
  intros i l max Hpre Hi Hnot.
  unfold can_arrange_prefix in *.
  destruct Hpre as [Hibound [Hmax [Hmaxhit Hall]]].
  repeat split; try lia; try assumption.
  intros j Hj Hhit.
  assert (j < i \/ j = i) as [Hlt | Heq] by lia.
  - apply Hall; [lia | assumption].
  - subst j. contradiction.
Qed.

Lemma can_arrange_prefix_update : forall i l max,
  can_arrange_prefix i l max ->
  0 <= i < Zlength l ->
  can_arrange_hit l i ->
  can_arrange_prefix (i + 1) l i.
Proof.
  intros i l max Hpre Hi Hhit.
  unfold can_arrange_prefix in *.
  destruct Hpre as [Hibound [_ [_ Hall]]].
  split; [lia |].
  split; [lia |].
  split; [right; exact Hhit |].
  intros j Hj Hjhit.
  assert (j < i \/ j = i) as [Hlt | Heq] by lia.
  - pose proof (Hall j ltac:(lia) Hjhit). lia.
  - lia.
Qed.

Lemma can_arrange_hit_of_cond : forall l i,
  0 <= i < Zlength l ->
  Znth i l 0 <= i ->
  can_arrange_hit l i.
Proof.
  intros l i Hi Hle.
  unfold can_arrange_hit.
  split; lia.
Qed.

Lemma can_arrange_not_hit_of_cond : forall l i,
  0 <= i < Zlength l ->
  Znth i l 0 > i ->
  ~ can_arrange_hit l i.
Proof.
  intros l i Hi Hgt Hhit.
  unfold can_arrange_hit in Hhit.
  lia.
Qed.

Lemma can_arrange_prefix_full_spec : forall l r,
  can_arrange_prefix (Zlength l) l r ->
  problem_135_spec l r.
Proof.
  intros l r Hpre.
  unfold can_arrange_prefix in Hpre.
  destruct Hpre as [Hibound [Hr [Hrhit Hmax]]].
  destruct Hrhit as [Hrneg | Hrhit].
  - left.
    split; [assumption |].
    intros k Hhit.
    unfold can_arrange_hit in Hhit.
    pose proof (Hmax k ltac:(lia) Hhit).
    lia.
  - right.
    exists r.
    split; [reflexivity |].
    split; [assumption |].
    intros j Hhit.
    unfold can_arrange_hit in Hhit.
    pose proof (Hmax j ltac:(lia) Hhit).
    lia.
Qed.

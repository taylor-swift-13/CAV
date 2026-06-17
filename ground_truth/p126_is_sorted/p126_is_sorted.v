(* spec/126 *)
(* Given a list of numbers, return whether or not they are sorted
in ascending order. If list has more than 1 duplicate of the same
number, return False. Assume no negative numbers and only integers.

Examples
is_sorted([5]) ➞ True
is_sorted([1, 2, 3, 4, 5]) ➞ True
is_sorted([1, 3, 2, 4, 5]) ➞ False
is_sorted([1, 2, 3, 4, 5, 6]) ➞ True
is_sorted([1, 2, 3, 4, 5, 6, 7]) ➞ True
is_sorted([1, 3, 2, 4, 5, 6, 7]) ➞ False
is_sorted([1, 2, 2, 3, 3, 4]) ➞ True
is_sorted([1, 2, 2, 2, 3, 4]) ➞ False *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* 仅非负整数（nat 已满足），无额外约束 *)

Definition sorted_no_triple_nat (l : list nat) : Prop :=
  (forall j, (1 <= j < length l)%nat ->
    nth (j - 1) l 0 <= nth j l 0) /\
  (forall j, (2 <= j < length l)%nat ->
    ~ (nth j l 0 = nth (j - 1) l 0 /\
       nth j l 0 = nth (j - 2) l 0)).

(* 程序规约 (Spec) *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition problem_126_pre (l : list Z) : Prop :=
  Forall (fun z => 0 <= z) l /\
  True.

Definition sorted_no_triple_prefix (i : Z) (l : list Z) : Prop :=
  (forall j, 1 <= j < i -> Znth (j - 1) l 0 <= Znth j l 0) /\
  (forall j, 2 <= j < i ->
    ~ (Znth j l 0 = Znth (j - 1) l 0 /\ Znth j l 0 = Znth (j - 2) l 0)).

Definition problem_126_spec (l : list Z) (b : bool) : Prop :=
  (sorted_no_triple_prefix (Zlength l) l <-> b = true).

Lemma sorted_no_triple_prefix_1 : forall l,
  sorted_no_triple_prefix 1 l.
Proof.
  intros l.
  unfold sorted_no_triple_prefix.
  split; intros j Hj; lia.
Qed.

Lemma sorted_no_triple_prefix_step : forall l i,
  1 <= i ->
  sorted_no_triple_prefix i l ->
  Znth (i - 1) l 0 <= Znth i l 0 ->
  ~ (2 <= i /\ Znth i l 0 = Znth (i - 1) l 0 /\ Znth i l 0 = Znth (i - 2) l 0) ->
  sorted_no_triple_prefix (i + 1) l.
Proof.
  intros l i Hi [Hsorted Htriple] Hle Hnot.
  unfold sorted_no_triple_prefix.
  split.
  - intros j Hj.
    destruct (Z.eq_dec j i) as [-> | Hne].
    + exact Hle.
    + apply Hsorted. lia.
  - intros j Hj.
    destruct (Z.eq_dec j i) as [-> | Hne].
    + intro Hbad. apply Hnot. tauto.
    + apply Htriple. lia.
Qed.

Lemma problem_126_spec_true_of_exit : forall l i,
  problem_126_pre l ->
  i >= Zlength l ->
  i <= Zlength l ->
  sorted_no_triple_prefix i l ->
  problem_126_spec l true.
Proof.
  intros l i _ Hge Hle Hprefix.
  replace i with (Zlength l) in Hprefix by lia.
  unfold problem_126_spec.
  split; intros _.
  - reflexivity.
  - exact Hprefix.
Qed.

Lemma problem_126_spec_false_of_desc : forall l i,
  problem_126_pre l ->
  1 <= i ->
  i < Zlength l ->
  Znth i l 0 < Znth (i - 1) l 0 ->
  problem_126_spec l false.
Proof.
  intros l i _ Hi Hlen Hlt.
  unfold problem_126_spec.
  split.
  - intros [Hsorted _].
    pose proof (Hsorted i ltac:(lia)).
    lia.
  - discriminate.
Qed.

Lemma problem_126_spec_false_of_triple : forall l i,
  problem_126_pre l ->
  2 <= i ->
  i < Zlength l ->
  Znth i l 0 = Znth (i - 1) l 0 ->
  Znth i l 0 = Znth (i - 2) l 0 ->
  problem_126_spec l false.
Proof.
  intros l i _ Hi Hlen Heq1 Heq2.
  unfold problem_126_spec.
  split.
  - intros [_ Htriple].
    exfalso.
    apply (Htriple i ltac:(lia)).
    split; assumption.
  - discriminate.
Qed.

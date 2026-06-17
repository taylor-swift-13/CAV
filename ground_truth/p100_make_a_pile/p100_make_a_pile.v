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

Lemma make_pile_Zlength : forall n,
  0 <= n ->
  Zlength (make_pile n) = n.
Proof.
  intros n Hn.
  unfold make_pile.
  rewrite Zlength_correct.
  rewrite length_map, Zseq_length.
  lia.
Qed.

Lemma make_pile_Znth : forall n i,
  0 <= i < n ->
  Znth i (make_pile n) 0 = n + 2 * i.
Proof.
  intros n i Hi.
  unfold make_pile.
  unfold Znth.
  eapply nth_error_nth.
  rewrite nth_error_map.
  rewrite nth_error_nth' with (d := 0%Z).
  - rewrite Zseq_nth by lia.
    rewrite Z2Nat.id by lia.
    reflexivity.
  - rewrite Zseq_length.
    lia.
Qed.

Lemma make_pile_sublist_snoc : forall n i,
  0 <= i < n ->
  sublist 0 (i + 1) (make_pile n) =
  sublist 0 i (make_pile n) ++ (n + 2 * i) :: nil.
Proof.
  intros n i Hi.
  pose proof (make_pile_Zlength n ltac:(lia)) as Hlen.
  assert (Hsplit_lo : 0 <= 0 <= i) by lia.
  assert (Hsplit_hi : i <= i + 1 <= Zlength (make_pile n))
    by (rewrite Hlen; lia).
  rewrite (@sublist_split Z 0 (i + 1) i (make_pile n) Hsplit_lo Hsplit_hi).
  rewrite (sublist_single 0 i (make_pile n)).
  - rewrite make_pile_Znth by lia.
    reflexivity.
  - rewrite Hlen.
    lia.
Qed.

Lemma problem_100_spec_make_pile : forall n,
  n > 0 ->
  problem_100_spec n (make_pile n).
Proof.
  intros n Hn.
  unfold problem_100_spec.
  split; [lia |].
  split.
  - apply make_pile_Zlength. lia.
  - intros i Hi.
    apply make_pile_Znth. lia.
Qed.

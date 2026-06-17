(* spec/82 *)
(* def prime_length(string):
"""Write a function that takes a string and returns True if the string
length is a prime number or False otherwise
Examples
prime_length('Hello') == True
prime_length('abcdcba') == True
prime_length('kittens') == True
prime_length('orange') == False
""" *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
From AUXLib Require Import ListLib.
Import ListNotations.

Local Open Scope Z_scope.

Definition prime_prefix (i n : Z) : Prop :=
  forall d, 2 <= d < i -> Z.rem n d <> 0.

Definition prime_len (n : Z) : Prop :=
  2 <= n /\ forall d, 2 <= d /\ d * d <= n -> Z.rem n d <> 0.

Definition bool_of (z : Z) : bool :=
  Z.eqb z 1.

Definition problem_82_pre (s : list Z) : Prop :=
  True.

Definition problem_82_spec (s : list Z) (output : Z) : Prop :=
  bool_of output = true <-> prime_len (Zlength s).

Lemma prime_prefix_2 : forall n,
  prime_prefix 2 n.
Proof.
  unfold prime_prefix.
  intros n d H.
  lia.
Qed.

Lemma prime_prefix_step : forall i n,
  prime_prefix i n ->
  Z.rem n i <> 0 ->
  prime_prefix (i + 1) n.
Proof.
  unfold prime_prefix.
  intros i n Hpre Hmod d Hd.
  destruct (Z.eq_dec d i) as [-> | Hne].
  - exact Hmod.
  - apply Hpre.
    lia.
Qed.

Lemma prime_len_false_small : forall n,
  n < 2 ->
  ~ prime_len n.
Proof.
  unfold prime_len.
  intros n Hlt H.
  lia.
Qed.

Lemma prime_len_false_divisor : forall i n,
  2 <= i ->
  i * i <= n ->
  Z.rem n i = 0 ->
  ~ prime_len n.
Proof.
  unfold prime_len.
  intros i n Hi Hsquare Hmod [_ Hprime].
  specialize (Hprime i ltac:(lia)).
  contradiction.
Qed.

Lemma prime_len_true_from_prefix : forall i n,
  2 <= n ->
  2 <= i ->
  i * i > n ->
  prime_prefix i n ->
  prime_len n.
Proof.
  unfold prime_prefix, prime_len.
  intros i n Hn Hi Hexit Hpre.
  split; [assumption |].
  intros d [Hd Hsquare].
  apply Hpre.
  assert (d < i) by nia.
  lia.
Qed.

Lemma problem_82_spec_true : forall s,
  prime_len (Zlength s) ->
  problem_82_spec s 1.
Proof.
  intros s H.
  unfold problem_82_spec, bool_of.
  change (Z.eqb 1 1) with true.
  split; intros _; [exact H | reflexivity].
Qed.

Lemma problem_82_spec_false : forall s,
  ~ prime_len (Zlength s) ->
  problem_82_spec s 0.
Proof.
  intros s H.
  unfold problem_82_spec, bool_of.
  change (Z.eqb 0 1) with false.
  split; intros Hbad.
  - discriminate.
  - exfalso. apply H. exact Hbad.
Qed.

Lemma prime_loop_next_bound : forall i n,
  2 <= i ->
  i <= 46340 ->
  n <= 2147302921 ->
  i * i <= n ->
  i + 1 <= 46340.
Proof.
  intros.
  nia.
Qed.

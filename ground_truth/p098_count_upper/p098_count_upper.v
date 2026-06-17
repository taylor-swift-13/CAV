(* spec/98 *)
(* def count_upper(s):
"""
Given a string s, count the number of uppercase vowels in even indices.

For example:
count_upper('aBCdEf') returns 1
count_upper('abcdefg') returns 0
count_upper('dBBE') returns 0
""" *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.
Import ListNotations.

Local Open Scope Z_scope.

Definition is_upper_vowel (x : Z) : bool :=
  Z.eqb x 65 || Z.eqb x 69 || Z.eqb x 73 || Z.eqb x 79 || Z.eqb x 85.

Definition is_even_index (i : Z) : bool :=
  Z.eqb (Z.rem i 2) 0.

Fixpoint count_upper_even_upto_nat (n : nat) (l : list Z) : Z :=
  match n with
  | O => 0
  | S n' =>
      let s := count_upper_even_upto_nat n' l in
      let i := Z.of_nat n' in
      if andb (is_even_index i) (is_upper_vowel (Znth i l 0))
      then s + 1
      else s
  end.

Definition count_upper_even_upto (i : Z) (l : list Z) : Z :=
  count_upper_even_upto_nat (Z.to_nat i) l.

Fixpoint count_upper_even_from (i : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs =>
      (if andb (is_even_index i) (is_upper_vowel x) then 1 else 0) +
      count_upper_even_from (i + 1) xs
  end.

Definition problem_98_pre (s : list Z) : Prop :=
  True.

Definition problem_98_spec (s : list Z) (output : Z) : Prop :=
  output = count_upper_even_from 0 s.

Lemma count_upper_even_upto_0 : forall l,
  count_upper_even_upto 0 l = 0.
Proof.
  intros l.
  unfold count_upper_even_upto.
  reflexivity.
Qed.

Lemma is_upper_vowel_true : forall x,
  x = 65 \/ x = 69 \/ x = 73 \/ x = 79 \/ x = 85 ->
  is_upper_vowel x = true.
Proof.
  intros x Hx.
  unfold is_upper_vowel.
  destruct Hx as [-> | [-> | [-> | [-> | ->]]]];
    repeat rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma is_upper_vowel_false : forall x,
  x <> 65 -> x <> 69 -> x <> 73 -> x <> 79 -> x <> 85 ->
  is_upper_vowel x = false.
Proof.
  intros x H65 H69 H73 H79 H85.
  unfold is_upper_vowel.
  repeat match goal with
  | |- context[Z.eqb ?a ?b] =>
      replace (Z.eqb a b) with false by (symmetry; apply Z.eqb_neq; lia)
  end.
  reflexivity.
Qed.

Lemma is_even_index_true : forall i,
  Z.rem i 2 = 0 ->
  is_even_index i = true.
Proof.
  intros i Hi.
  unfold is_even_index.
  rewrite Hi, Z.eqb_refl.
  reflexivity.
Qed.

Lemma is_even_index_false : forall i,
  Z.rem i 2 <> 0 ->
  is_even_index i = false.
Proof.
  intros i Hi.
  unfold is_even_index.
  apply Z.eqb_neq.
  exact Hi.
Qed.

Lemma count_upper_even_upto_step_hit : forall i l,
  0 <= i ->
  Z.rem i 2 = 0 ->
  (Znth i l 0 = 65 \/ Znth i l 0 = 69 \/ Znth i l 0 = 73 \/
   Znth i l 0 = 79 \/ Znth i l 0 = 85) ->
  count_upper_even_upto (i + 1) l =
  count_upper_even_upto i l + 1.
Proof.
  intros i l Hi Heven Hhit.
  unfold count_upper_even_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  rewrite is_even_index_true by exact Heven.
  rewrite is_upper_vowel_true by exact Hhit.
  reflexivity.
Qed.

Lemma count_upper_even_upto_step_even_miss : forall i l,
  0 <= i ->
  Z.rem i 2 = 0 ->
  Znth i l 0 <> 65 -> Znth i l 0 <> 69 -> Znth i l 0 <> 73 ->
  Znth i l 0 <> 79 -> Znth i l 0 <> 85 ->
  count_upper_even_upto (i + 1) l =
  count_upper_even_upto i l.
Proof.
  intros i l Hi Heven H65 H69 H73 H79 H85.
  unfold count_upper_even_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  rewrite is_even_index_true by exact Heven.
  rewrite is_upper_vowel_false by auto.
  reflexivity.
Qed.

Lemma count_upper_even_upto_step_odd : forall i l,
  0 <= i ->
  Z.rem i 2 <> 0 ->
  count_upper_even_upto (i + 1) l =
  count_upper_even_upto i l.
Proof.
  intros i l Hi Hodd.
  unfold count_upper_even_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  rewrite is_even_index_false by exact Hodd.
  reflexivity.
Qed.

Lemma count_upper_even_upto_nat_app_unchanged : forall n l x,
  (n <= length l)%nat ->
  count_upper_even_upto_nat n (l ++ [x]) =
  count_upper_even_upto_nat n l.
Proof.
  induction n as [| n IH]; intros l x Hn.
  - reflexivity.
  - simpl.
    rewrite IH by lia.
    rewrite app_Znth1 by (rewrite Zlength_correct; lia).
    reflexivity.
Qed.

Lemma count_upper_even_upto_Zlength_app_single : forall l x,
  count_upper_even_upto (Zlength (l ++ [x])) (l ++ [x]) =
  count_upper_even_upto (Zlength l) l +
  (if andb (is_even_index (Zlength l)) (is_upper_vowel x) then 1 else 0).
Proof.
  intros l x.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  unfold count_upper_even_upto.
  replace (Zlength l + Z.succ 0) with (Z.of_nat (S (length l)))
    by (rewrite Zlength_correct; lia).
  rewrite Nat2Z.id.
  replace (Z.to_nat (Zlength l)) with (length l)
    by (rewrite Zlength_correct; lia).
  simpl.
  replace (Z.of_nat (length l)) with (Zlength l)
    by (rewrite Zlength_correct; lia).
  rewrite (count_upper_even_upto_nat_app_unchanged (length l) l x)
    by apply Nat.le_refl.
  rewrite app_Znth2 by lia.
  replace (Zlength l - Zlength l) with 0 by lia.
  simpl.
  change (Znth 0 [x] 0) with x.
  destruct (is_even_index (Zlength l) && is_upper_vowel x).
  - reflexivity.
  - rewrite Z.add_0_r. reflexivity.
Qed.

Lemma count_upper_even_from_app_single : forall i l x,
  count_upper_even_from i (l ++ [x]) =
  count_upper_even_from i l +
  (if andb (is_even_index (i + Zlength l)) (is_upper_vowel x) then 1 else 0).
Proof.
  intros i l.
  revert i.
  induction l as [| a l IH]; intros i x.
  - simpl. rewrite Zlength_nil. replace (i + 0) with i by lia.
    rewrite Z.add_0_r. reflexivity.
  - simpl.
    rewrite (IH (i + 1) x).
    rewrite Zlength_cons.
    replace (i + Z.succ (Zlength l)) with (i + 1 + Zlength l) by lia.
    remember (is_even_index (i + 1 + Zlength l) && is_upper_vowel x) as b.
    destruct b; lia.
Qed.

Lemma count_upper_even_upto_Zlength_eq_from : forall l,
  count_upper_even_upto (Zlength l) l =
  count_upper_even_from 0 l.
Proof.
  induction l using rev_ind.
  - reflexivity.
  - rewrite count_upper_even_upto_Zlength_app_single.
    rewrite count_upper_even_from_app_single.
    rewrite IHl.
    replace (0 + Zlength l) with (Zlength l) by lia.
    reflexivity.
Qed.

Lemma problem_98_spec_intro : forall s output,
  output = count_upper_even_upto (Zlength s) s ->
  problem_98_spec s output.
Proof.
  intros s output Hout.
  unfold problem_98_spec.
  rewrite Hout.
  apply count_upper_even_upto_Zlength_eq_from.
Qed.

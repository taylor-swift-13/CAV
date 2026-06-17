(* spec/134 *)
(* def check_if_last_char_is_a_letter(txt):
'''
Create a function that returns True if the last character
of a given string is an alphabetical character and is not
a part of a word, and False otherwise.
Note: "word" is a group of characters separated by space.

Examples:
check_if_last_char_is_a_letter("apple pie") ➞ False
check_if_last_char_is_a_letter("apple pi e") ➞ True
check_if_last_char_is_a_letter("apple pi e ") ➞ False
check_if_last_char_is_a_letter("") ➞ False
''' *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Import ListNotations.

Local Open Scope Z_scope.

Definition is_alpha (x : Z) : Prop :=
  65 <= x <= 90 \/ 97 <= x <= 122.

Definition ascii_range (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0 <= 127.

Definition bool_of (z : Z) : bool :=
  Z.eqb z 1.

Definition ends_with_single_letter (l : list Z) : Prop :=
  1 <= Zlength l /\
  is_alpha (Znth (Zlength l - 1) l 0) /\
  (Zlength l = 1 \/ Znth (Zlength l - 2) l 0 = 32).

Definition problem_134_pre (s : list Z) : Prop :=
  True.

Definition problem_134_spec (s : list Z) (output : Z) : Prop :=
  bool_of output = true <-> ends_with_single_letter s.

Lemma problem_134_spec_true : forall s,
  ends_with_single_letter s ->
  problem_134_spec s 1.
Proof.
  intros s H.
  unfold problem_134_spec, bool_of.
  simpl.
  split; auto.
Qed.

Lemma problem_134_spec_false : forall s,
  ~ ends_with_single_letter s ->
  problem_134_spec s 0.
Proof.
  intros s H.
  unfold problem_134_spec, bool_of.
  simpl.
  split; intro Hfalse; try discriminate.
  contradiction.
Qed.

Lemma ends_with_single_letter_intro_single : forall s,
  Zlength s = 1 ->
  is_alpha (Znth (Zlength s - 1) s 0) ->
  ends_with_single_letter s.
Proof.
  intros s Hlen Halpha.
  unfold ends_with_single_letter.
  repeat split; try assumption; lia.
Qed.

Lemma ends_with_single_letter_intro_space : forall s,
  1 < Zlength s ->
  is_alpha (Znth (Zlength s - 1) s 0) ->
  Znth (Zlength s - 2) s 0 = 32 ->
  ends_with_single_letter s.
Proof.
  intros s Hlen Halpha Hspace.
  unfold ends_with_single_letter.
  repeat split; try assumption; lia.
Qed.

Lemma not_ends_with_single_letter_empty : forall s,
  Zlength s = 0 ->
  ~ ends_with_single_letter s.
Proof.
  unfold ends_with_single_letter.
  intros s Hlen H.
  lia.
Qed.

Lemma not_ends_with_single_letter_not_alpha : forall s,
  1 <= Zlength s ->
  ~ is_alpha (Znth (Zlength s - 1) s 0) ->
  ~ ends_with_single_letter s.
Proof.
  unfold ends_with_single_letter.
  intros s Hlen Hnot H.
  tauto.
Qed.

Lemma not_ends_with_single_letter_prev_not_space : forall s,
  1 < Zlength s ->
  is_alpha (Znth (Zlength s - 1) s 0) ->
  Znth (Zlength s - 2) s 0 <> 32 ->
  ~ ends_with_single_letter s.
Proof.
  unfold ends_with_single_letter.
  intros s Hlen _ Hnot H.
  destruct H as [_ [_ [Hsingle | Hspace]]].
  - lia.
  - contradiction.
Qed.

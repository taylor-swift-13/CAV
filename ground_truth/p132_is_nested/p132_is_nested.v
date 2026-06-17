(* spec/132 *)
(* def is_nested(string):
'''
Create a function that takes a string as input which contains only square brackets.
The function should return True if and only if there is a valid subsequence of brackets
where at least one bracket in the subsequence is nested.

is_nested('[[]]') ➞ True
is_nested('[]]]]]]][[[[[]') ➞ False
is_nested('[][]') ➞ False
is_nested('[]') ➞ False
is_nested('[[][]]') ➞ True
is_nested('[[]][[') ➞ True
''' *)
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Export string_bridge.

Local Open Scope Z_scope.

Definition bracket_char (c : Z) : Prop :=
  c = 91 \/ c = 93.

Definition bool_of (z : Z) : bool :=
  Z.eqb z 1.

Definition subseq_step (state c : Z) : Z :=
  if Z.eqb state 0 then
    if Z.eqb c 91 then 1 else 0
  else if Z.eqb state 1 then
    if Z.eqb c 91 then 2 else 1
  else if Z.eqb state 2 then
    if Z.eqb c 93 then 3 else 2
  else if Z.eqb state 3 then
    if Z.eqb c 93 then 4 else 3
  else 4.

Fixpoint subseq_state_list (state : Z) (s : list Z) : Z :=
  match s with
  | [] => state
  | c :: rest => subseq_state_list (subseq_step state c) rest
  end.

Definition subseq_state_prefix (i : Z) (s : list Z) : Z :=
  subseq_state_list 0 (firstn (Z.to_nat i) s).

Definition problem_132_pre (s : list Z) : Prop :=
  Forall bracket_char s.

Definition problem_132_spec (s : list Z) (output : Z) : Prop :=
  bool_of output = true <-> subseq_state_list 0 s = 4.

Lemma subseq_state_list_app : forall a b st,
  subseq_state_list st (List.app a b) =
  subseq_state_list (subseq_state_list st a) b.
Proof.
  induction a as [| c rest IH]; intros b st; simpl; auto.
Qed.

Lemma firstn_succ_nth_132 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = List.app (firstn n l) [nth n l d].
Proof.
  induction n as [| n IH]; intros l d Hlen.
  - destruct l as [| x xs]; simpl in *; try lia; reflexivity.
  - destruct l as [| x xs]; simpl in *; try lia.
    f_equal.
    apply IH.
    lia.
Qed.

Lemma firstn_succ_Znth_132 : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  List.app (firstn (Z.to_nat i) l) [Znth i l d].
Proof.
  intros l i d Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite (firstn_succ_nth_132 (Z.to_nat i) l d).
  - unfold Znth.
    reflexivity.
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
Qed.

Lemma subseq_state_prefix_step : forall s i,
  0 <= i < Zlength s ->
  subseq_state_prefix (i + 1) s =
  subseq_step (subseq_state_prefix i s) (Znth i s 0).
Proof.
  intros s i Hi.
  unfold subseq_state_prefix.
  rewrite (firstn_succ_Znth_132 s i 0) by exact Hi.
  rewrite subseq_state_list_app.
  reflexivity.
Qed.

Lemma subseq_step_range : forall state c,
  0 <= state <= 4 ->
  0 <= subseq_step state c <= 4.
Proof.
  intros state c Hstate.
  unfold subseq_step.
  repeat match goal with
  | |- context[Z.eqb ?a ?b] => destruct (Z.eqb_spec a b); subst
  end; lia.
Qed.

Lemma subseq_state_list_range : forall l state,
  0 <= state <= 4 ->
  0 <= subseq_state_list state l <= 4.
Proof.
  induction l as [| c rest IH]; intros state Hstate; simpl.
  - exact Hstate.
  - apply IH.
    apply subseq_step_range.
    exact Hstate.
Qed.

Lemma subseq_state_prefix_range : forall s i,
  0 <= subseq_state_prefix i s <= 4.
Proof.
  intros s i.
  unfold subseq_state_prefix.
  apply subseq_state_list_range.
  lia.
Qed.

Lemma subseq_state_prefix_full : forall s i,
  i = Zlength s ->
  subseq_state_prefix i s = subseq_state_list 0 s.
Proof.
  intros s i Hi.
  unfold subseq_state_prefix.
  rewrite Hi.
  rewrite firstn_all2; auto.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  lia.
Qed.

Lemma problem_132_spec_true : forall s,
  subseq_state_list 0 s = 4 ->
  problem_132_spec s 1.
Proof.
  intros s Hstate.
  unfold problem_132_spec, bool_of.
  simpl.
  split; auto.
Qed.

Lemma problem_132_spec_false : forall s,
  subseq_state_list 0 s <> 4 ->
  problem_132_spec s 0.
Proof.
  intros s Hstate.
  unfold problem_132_spec, bool_of.
  simpl.
  split; intro H; try discriminate.
  contradiction.
Qed.

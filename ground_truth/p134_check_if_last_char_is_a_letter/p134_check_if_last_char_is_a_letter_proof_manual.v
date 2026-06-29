Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p134_check_if_last_char_is_a_letter Require Import p134_check_if_last_char_is_a_letter_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p134_check_if_last_char_is_a_letter.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p134_check_if_last_char_is_a_letter.v so public contract files expose definitions only. *)

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


Ltac c134_pre :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia.

Ltac c134_alpha :=
  unfold is_alpha in *; lia.

Lemma proof_of_p134_check_if_last_char_is_a_letter_entail_wit_1_1 : p134_check_if_last_char_is_a_letter_entail_wit_1_1.
Proof.
  unfold p134_check_if_last_char_is_a_letter_entail_wit_1_1.
  intros.
  c134_pre.
  entailer!.
  try c134_alpha.
Qed.

Lemma proof_of_p134_check_if_last_char_is_a_letter_entail_wit_1_2 : p134_check_if_last_char_is_a_letter_entail_wit_1_2.
Proof.
  unfold p134_check_if_last_char_is_a_letter_entail_wit_1_2.
  intros.
  c134_pre.
  entailer!.
  try c134_alpha.
Qed.

Lemma proof_of_p134_check_if_last_char_is_a_letter_return_wit_1 : p134_check_if_last_char_is_a_letter_return_wit_1.
Proof.
  unfold p134_check_if_last_char_is_a_letter_return_wit_1.
  intros.
  c134_pre.
  entailer!.
  eapply problem_134_spec_false; eauto.
  apply not_ends_with_single_letter_prev_not_space; auto; lia.
Qed.

Lemma proof_of_p134_check_if_last_char_is_a_letter_return_wit_2 : p134_check_if_last_char_is_a_letter_return_wit_2.
Proof.
  unfold p134_check_if_last_char_is_a_letter_return_wit_2.
  intros.
  c134_pre.
  entailer!.
  eapply problem_134_spec_true; eauto.
  apply ends_with_single_letter_intro_space; auto; lia.
Qed.

Lemma proof_of_p134_check_if_last_char_is_a_letter_return_wit_3 : p134_check_if_last_char_is_a_letter_return_wit_3.
Proof.
  unfold p134_check_if_last_char_is_a_letter_return_wit_3.
  intros.
  c134_pre.
  entailer!.
  eapply problem_134_spec_true; eauto.
  apply ends_with_single_letter_intro_single; try lia.
  unfold is_alpha.
  replace (Zlength l - 1) with 0 by lia.
  replace (1 - 1) with 0 in * by lia.
  left; lia.
Qed.

Lemma proof_of_p134_check_if_last_char_is_a_letter_return_wit_4 : p134_check_if_last_char_is_a_letter_return_wit_4.
Proof.
  unfold p134_check_if_last_char_is_a_letter_return_wit_4.
  intros.
  c134_pre.
  entailer!.
  eapply problem_134_spec_true; eauto.
  apply ends_with_single_letter_intro_single; try lia.
  unfold is_alpha.
  replace (Zlength l - 1) with 0 by lia.
  replace (1 - 1) with 0 in * by lia.
  right; lia.
Qed.

Lemma proof_of_p134_check_if_last_char_is_a_letter_return_wit_5 : p134_check_if_last_char_is_a_letter_return_wit_5.
Proof.
  unfold p134_check_if_last_char_is_a_letter_return_wit_5.
  intros.
  c134_pre.
  entailer!.
  eapply problem_134_spec_false; eauto.
  apply not_ends_with_single_letter_not_alpha; try lia.
  unfold is_alpha.
  lia.
Qed.

Lemma proof_of_p134_check_if_last_char_is_a_letter_return_wit_6 : p134_check_if_last_char_is_a_letter_return_wit_6.
Proof.
  unfold p134_check_if_last_char_is_a_letter_return_wit_6.
  intros.
  c134_pre.
  entailer!.
  eapply problem_134_spec_false; eauto.
  apply not_ends_with_single_letter_not_alpha; try lia.
  unfold is_alpha.
  lia.
Qed.

Lemma proof_of_p134_check_if_last_char_is_a_letter_return_wit_7 : p134_check_if_last_char_is_a_letter_return_wit_7.
Proof.
  unfold p134_check_if_last_char_is_a_letter_return_wit_7.
  intros.
  c134_pre.
  entailer!.
  eapply problem_134_spec_false; eauto.
  apply not_ends_with_single_letter_not_alpha; try lia.
  unfold is_alpha.
  lia.
Qed.

Lemma proof_of_p134_check_if_last_char_is_a_letter_return_wit_8 : p134_check_if_last_char_is_a_letter_return_wit_8.
Proof.
  unfold p134_check_if_last_char_is_a_letter_return_wit_8.
  intros.
  c134_pre.
  entailer!.
  eapply problem_134_spec_false; eauto.
  apply not_ends_with_single_letter_empty.
  lia.
Qed.

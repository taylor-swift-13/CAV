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
From SimpleC.EE.CAV.ground_truth_p118_get_closest_vowel Require Import p118_get_closest_vowel_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Arith.
Require Import Coq.Logic.FunctionalExtensionality.

Import naive_C_Rules.
Require Import p118_get_closest_vowel.
Local Open Scope sac.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope list_scope.

(* Proof helpers moved from p118_get_closest_vowel.v so public contract files expose definitions only. *)

Lemma no_candidate_after_step : forall i l,
  ~ closest_vowel_candidate l i ->
  no_candidate_after i l ->
  no_candidate_after (i - 1) l.
Proof.
  unfold no_candidate_after.
  intros i l Hnot Hafter j Hj.
  destruct (Z.eq_dec j i) as [-> | Hne].
  - exact Hnot.
  - apply Hafter. lia.
Qed.
Lemma no_candidate_after_start : forall l,
  no_candidate_after (Zlength l - 2) l.
Proof.
  unfold no_candidate_after.
  intros l j Hj.
  lia.
Qed.
Lemma problem_118_spec_found : forall l i,
  closest_vowel_candidate l i ->
  no_candidate_after i l ->
  problem_118_spec l [Znth i l 0].
Proof.
  intros l i Hcand Hafter.
  unfold problem_118_spec.
  left.
  exists i.
  split; [exact Hcand |].
  split; [exact Hafter | reflexivity].
Qed.
Lemma problem_118_spec_not_found : forall l,
  no_candidate_after 0 l ->
  problem_118_spec l [].
Proof.
  intros l Hnone.
  unfold problem_118_spec.
  right.
  split.
  - intros i Hi.
    apply Hnone. lia.
  - reflexivity.
Qed.
Lemma alpha_range_nonzero : forall l k,
  alpha_range l ->
  0 <= k < Zlength l ->
  Znth k l 0 <> 0.
Proof.
  intros l k Halpha Hk.
  specialize (Halpha k Hk).
  unfold is_alpha in Halpha.
  lia.
Qed.


Ltac c118_base :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia;
  entailer!;
  try (unfold is_vowel, is_consonant, is_alpha in *; lia).

Ltac c118_left_branch :=
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros1];
  entailer!;
  unfold is_vowel, is_consonant, is_alpha in *; lia.

Ltac c118_right_branch :=
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2];
  entailer!;
  unfold is_vowel, is_consonant, is_alpha in *; lia.

Ltac c118_nonzero :=
  match goal with
  | Halpha : alpha_range ?l |-
      forall k : Z, 0 <= k < Zlength ?l -> Znth k ?l 0 <> 0 =>
      intros k Hk; eapply alpha_range_nonzero; eauto
  | Halpha : alpha_range ?l |-
      forall k : Z, 0 <= k < 1 -> Znth k (Znth ?i ?l 0 :: nil) 0 <> 0 =>
      intros k Hk;
      assert (k = 0) by lia;
      subst k;
      rewrite Znth0_cons;
      eapply alpha_range_nonzero; eauto; lia
  end.

Lemma proof_of_is_vowel_code_return_wit_1 : is_vowel_code_return_wit_1.
Proof. unfold is_vowel_code_return_wit_1; intros; c118_base; c118_left_branch. Qed.

Lemma proof_of_is_vowel_code_return_wit_2 : is_vowel_code_return_wit_2.
Proof. unfold is_vowel_code_return_wit_2; intros; c118_base; c118_right_branch. Qed.

Lemma proof_of_is_vowel_code_return_wit_3 : is_vowel_code_return_wit_3.
Proof. unfold is_vowel_code_return_wit_3; intros; c118_base; c118_right_branch. Qed.

Lemma proof_of_is_vowel_code_return_wit_4 : is_vowel_code_return_wit_4.
Proof. unfold is_vowel_code_return_wit_4; intros; c118_base; c118_right_branch. Qed.

Lemma proof_of_is_vowel_code_return_wit_5 : is_vowel_code_return_wit_5.
Proof. unfold is_vowel_code_return_wit_5; intros; c118_base; c118_right_branch. Qed.

Lemma proof_of_is_vowel_code_return_wit_6 : is_vowel_code_return_wit_6.
Proof. unfold is_vowel_code_return_wit_6; intros; c118_base; c118_right_branch. Qed.

Lemma proof_of_is_vowel_code_return_wit_7 : is_vowel_code_return_wit_7.
Proof. unfold is_vowel_code_return_wit_7; intros; c118_base; c118_right_branch. Qed.

Lemma proof_of_is_vowel_code_return_wit_8 : is_vowel_code_return_wit_8.
Proof. unfold is_vowel_code_return_wit_8; intros; c118_base; c118_right_branch. Qed.

Lemma proof_of_is_vowel_code_return_wit_9 : is_vowel_code_return_wit_9.
Proof. unfold is_vowel_code_return_wit_9; intros; c118_base; c118_right_branch. Qed.

Lemma proof_of_is_vowel_code_return_wit_10 : is_vowel_code_return_wit_10.
Proof. unfold is_vowel_code_return_wit_10; intros; c118_base; c118_right_branch. Qed.

Lemma proof_of_is_vowel_code_return_wit_11 : is_vowel_code_return_wit_11.
Proof. unfold is_vowel_code_return_wit_11; intros; c118_base; c118_right_branch. Qed.

Lemma proof_of_p118_get_closest_vowel_entail_wit_1 : p118_get_closest_vowel_entail_wit_1.
Proof.
  unfold p118_get_closest_vowel_entail_wit_1.
  intros.
  pre_process; subst; entailer!.
  apply no_candidate_after_start.
Qed.

Lemma proof_of_p118_get_closest_vowel_entail_wit_2 : p118_get_closest_vowel_entail_wit_2.
Proof.
  unfold p118_get_closest_vowel_entail_wit_2.
  intros.
  c118_base.
  unfold closest_vowel_candidate, is_consonant.
  split.
  - lia.
  - split.
    + split.
      * apply H15. lia.
      * exact H1.
    + split.
      * exact H7.
      * split.
        -- apply H15. lia.
        -- exact H4.
Qed.

Lemma proof_of_p118_get_closest_vowel_entail_wit_3_1 : p118_get_closest_vowel_entail_wit_3_1.
Proof.
  unfold p118_get_closest_vowel_entail_wit_3_1.
  intros.
  c118_base.
  intro Hcand.
  unfold closest_vowel_candidate, is_consonant in Hcand.
  tauto.
Qed.

Lemma proof_of_p118_get_closest_vowel_entail_wit_3_2 : p118_get_closest_vowel_entail_wit_3_2.
Proof.
  unfold p118_get_closest_vowel_entail_wit_3_2.
  intros.
  c118_base.
  intro Hcand.
  unfold closest_vowel_candidate, is_consonant in Hcand.
  tauto.
Qed.

Lemma proof_of_p118_get_closest_vowel_entail_wit_3_3 : p118_get_closest_vowel_entail_wit_3_3.
Proof.
  unfold p118_get_closest_vowel_entail_wit_3_3.
  intros.
  c118_base.
  intro Hcand.
  unfold closest_vowel_candidate in Hcand.
  tauto.
Qed.

Lemma proof_of_p118_get_closest_vowel_entail_wit_4 : p118_get_closest_vowel_entail_wit_4.
Proof.
  unfold p118_get_closest_vowel_entail_wit_4.
  intros.
  c118_base.
  apply no_candidate_after_step; assumption.
Qed.

Lemma proof_of_p118_get_closest_vowel_entail_wit_5 : p118_get_closest_vowel_entail_wit_5.
Proof.
  unfold p118_get_closest_vowel_entail_wit_5.
  intros.
  pre_process; subst.
  assert (i = 0) by lia.
  subst i.
  entailer!.
Qed.

Lemma proof_of_p118_get_closest_vowel_return_wit_1 : p118_get_closest_vowel_return_wit_1.
Proof.
  unfold p118_get_closest_vowel_return_wit_1.
  intros.
  pre_process; subst.
  Exists (@nil Z) 0.
  rewrite (CharArray.undef_seg_empty retval 1).
  entailer!.
  all: try solve [apply problem_118_spec_not_found; assumption | c118_nonzero].
Qed.

Lemma proof_of_p118_get_closest_vowel_return_wit_2 : p118_get_closest_vowel_return_wit_2.
Proof.
  unfold p118_get_closest_vowel_return_wit_2.
  intros.
  pre_process; subst.
  repeat rewrite app_Znth1 in * by lia.
  replace (signed_last_nbits (Znth i l 0) 8) with (Znth i l 0).
  2:{
    symmetry.
    apply signed_last_nbits_eq.
    - lia.
    - match goal with
      | Halpha : alpha_range l |- _ =>
          assert (Halpha_i : is_alpha (Znth i l 0)) by (apply Halpha; lia)
      end.
      unfold is_alpha in Halpha_i.
      lia.
  }
  Exists ((Znth i l 0) :: nil) 1.
  rewrite (CharArray.undef_seg_empty retval 2).
  entailer!.
  all: try solve [apply problem_118_spec_found; assumption | c118_nonzero].
Qed.

Lemma proof_of_p118_get_closest_vowel_return_wit_3 : p118_get_closest_vowel_return_wit_3.
Proof.
  unfold p118_get_closest_vowel_return_wit_3.
  intros.
  pre_process; subst.
  Exists (@nil Z) 0.
  rewrite (CharArray.undef_seg_empty retval 1).
  entailer!.
  all: try solve [c118_nonzero].
  apply problem_118_spec_not_found.
  unfold no_candidate_after, closest_vowel_candidate.
    intros j Hj Hcand.
    lia.
Qed.

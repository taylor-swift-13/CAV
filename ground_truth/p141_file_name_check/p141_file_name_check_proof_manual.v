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
From SimpleC.EE.CAV.ground_truth_p141_file_name_check Require Import p141_file_name_check_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.

Import naive_C_Rules.
Require Import p141_file_name_check.
Local Open Scope sac.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope list_scope.

(* Proof helpers moved from p141_file_name_check.v so public contract files expose definitions only. *)

Lemma problem_141_spec_yes : forall l,
  file_name_checks l ->
  problem_141_spec l 1.
Proof.
  intros l Hvalid.
  unfold problem_141_spec.
  left.
  split; [exact Hvalid | reflexivity].
Qed.
Lemma problem_141_spec_no : forall l,
  ~ file_name_checks l ->
  problem_141_spec l 0.
Proof.
  intros l Hnot.
  unfold problem_141_spec.
  right.
  split; [exact Hnot | reflexivity].
Qed.
Lemma problem_141_spec_no_len_lt : forall l,
  Zlength l < 5 ->
  problem_141_spec l 0.
Proof.
  intros l Hlen.
  apply problem_141_spec_no.
  unfold file_name_checks.
  lia.
Qed.
Lemma problem_141_spec_no_not_alpha : forall l,
  ~ is_alpha (Znth 0 l 0) ->
  problem_141_spec l 0.
Proof.
  intros l Hnot.
  apply problem_141_spec_no.
  unfold file_name_checks.
  tauto.
Qed.
Lemma problem_141_spec_no_not_suffix : forall l,
  ~ suffix_ok l ->
  problem_141_spec l 0.
Proof.
  intros l Hnot.
  apply problem_141_spec_no.
  unfold file_name_checks.
  tauto.
Qed.
Lemma problem_141_spec_no_digit_gt : forall l,
  digit_count_upto (Zlength l) l > 3 ->
  problem_141_spec l 0.
Proof.
  intros l Hgt.
  apply problem_141_spec_no.
  unfold file_name_checks.
  lia.
Qed.
Lemma problem_141_spec_no_dot_ne : forall l,
  dot_count_upto (Zlength l) l <> 1 ->
  problem_141_spec l 0.
Proof.
  intros l Hne.
  apply problem_141_spec_no.
  unfold file_name_checks.
  lia.
Qed.
Lemma count_by_zb_nonneg : forall f l,
  0 <= count_by_zb f l.
Proof.
  intros f l.
  induction l; simpl; try lia.
  destruct (f a); lia.
Qed.
Lemma count_by_zb_le_len : forall f l,
  count_by_zb f l <= Zlength l.
Proof.
  intros f l.
  induction l; simpl.
  - rewrite Zlength_nil. lia.
  - rewrite Zlength_cons.
    destruct (f a); lia.
Qed.
Lemma count_by_zb_app_single : forall f l x,
  count_by_zb f (l ++ [x]) =
  count_by_zb f l + if f x then 1 else 0.
Proof.
  intros f l x.
  induction l; simpl.
  - lia.
  - rewrite IHl.
    destruct (f a); destruct (f x); lia.
Qed.
Lemma digit_count_upto_bounds : forall i l,
  0 <= i <= Zlength l ->
  0 <= digit_count_upto i l <= i.
Proof.
  intros i l Hi.
  unfold digit_count_upto.
  split.
  - apply count_by_zb_nonneg.
  - pose proof (count_by_zb_le_len is_digit_zb (sublist 0 i l)).
    rewrite Zlength_sublist in H by lia.
    lia.
Qed.
Lemma dot_count_upto_bounds : forall i l,
  0 <= i <= Zlength l ->
  0 <= dot_count_upto i l <= i.
Proof.
  intros i l Hi.
  unfold dot_count_upto.
  split.
  - apply count_by_zb_nonneg.
  - pose proof (count_by_zb_le_len is_dot_zb (sublist 0 i l)).
    rewrite Zlength_sublist in H by lia.
    lia.
Qed.
Lemma digit_count_upto_0 : forall l,
  digit_count_upto 0 l = 0.
Proof.
  intros l.
  unfold digit_count_upto, sublist.
  simpl.
  reflexivity.
Qed.
Lemma dot_count_upto_0 : forall l,
  dot_count_upto 0 l = 0.
Proof.
  intros l.
  unfold dot_count_upto, sublist.
  simpl.
  reflexivity.
Qed.
Lemma digit_count_upto_step_hit : forall i l,
  0 <= i < Zlength l ->
  is_digit (Znth i l 0) ->
  digit_count_upto (i + 1) l = digit_count_upto i l + 1.
Proof.
  intros i l Hi Hd.
  unfold digit_count_upto.
  rewrite (sublist_split 0 (i + 1) i l) by
    lia.
  rewrite (sublist_single 0 i l) by lia.
  rewrite count_by_zb_app_single.
  unfold is_digit, is_digit_zb in *.
  replace (Z.leb 48 (Znth i l 0)) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb (Znth i l 0) 57) with true by (symmetry; apply Z.leb_le; lia).
  simpl.
  lia.
Qed.
Lemma digit_count_upto_step_miss : forall i l,
  0 <= i < Zlength l ->
  ~ is_digit (Znth i l 0) ->
  digit_count_upto (i + 1) l = digit_count_upto i l.
Proof.
  intros i l Hi Hd.
  unfold digit_count_upto.
  rewrite (sublist_split 0 (i + 1) i l) by
    lia.
  rewrite (sublist_single 0 i l) by lia.
  rewrite count_by_zb_app_single.
  unfold is_digit, is_digit_zb in *.
  destruct (Z.leb_spec 48 (Znth i l 0));
    destruct (Z.leb_spec (Znth i l 0) 57); simpl; lia.
Qed.
Lemma dot_count_upto_step_hit : forall i l,
  0 <= i < Zlength l ->
  Znth i l 0 = 46 ->
  dot_count_upto (i + 1) l = dot_count_upto i l + 1.
Proof.
  intros i l Hi Hdot.
  unfold dot_count_upto.
  rewrite (sublist_split 0 (i + 1) i l) by
    lia.
  rewrite (sublist_single 0 i l) by lia.
  rewrite count_by_zb_app_single.
  unfold is_dot_zb.
  rewrite Hdot, Z.eqb_refl.
  simpl.
  lia.
Qed.
Lemma dot_count_upto_step_miss : forall i l,
  0 <= i < Zlength l ->
  Znth i l 0 <> 46 ->
  dot_count_upto (i + 1) l = dot_count_upto i l.
Proof.
  intros i l Hi Hdot.
  unfold dot_count_upto.
  rewrite (sublist_split 0 (i + 1) i l) by
    lia.
  rewrite (sublist_single 0 i l) by lia.
  rewrite count_by_zb_app_single.
  unfold is_dot_zb.
  replace (Z.eqb (Znth i l 0) 46) with false by
    (symmetry; apply Z.eqb_neq; lia).
  lia.
Qed.


Ltac c141_prep :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia.

Ltac c141_left :=
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros1];
  c141_prep;
  entailer!;
  try (unfold is_alpha in *; lia);
  try (unfold suffix_ok, suffix_txt, suffix_exe, suffix_dll in *;
       intro Hs; tauto || lia).

Ltac c141_right :=
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2];
  c141_prep;
  entailer!;
  try (unfold is_alpha in *; lia);
  try (unfold suffix_ok, suffix_txt, suffix_exe, suffix_dll in *; tauto).

Ltac c141_or :=
  first [solve [c141_right] | solve [c141_left]].

Lemma proof_of_p141_file_name_check_entail_wit_1_1 : p141_file_name_check_entail_wit_1_1.
Proof. unfold p141_file_name_check_entail_wit_1_1; intros; c141_or. Qed.

Lemma proof_of_p141_file_name_check_entail_wit_1_2 : p141_file_name_check_entail_wit_1_2.
Proof. unfold p141_file_name_check_entail_wit_1_2; intros; c141_or. Qed.

Lemma proof_of_p141_file_name_check_entail_wit_1_3 : p141_file_name_check_entail_wit_1_3.
Proof. unfold p141_file_name_check_entail_wit_1_3; intros; c141_or. Qed.

Lemma proof_of_p141_file_name_check_entail_wit_1_4 : p141_file_name_check_entail_wit_1_4.
Proof. unfold p141_file_name_check_entail_wit_1_4; intros; c141_or. Qed.

Lemma proof_of_p141_file_name_check_entail_wit_1_5 : p141_file_name_check_entail_wit_1_5.
Proof. unfold p141_file_name_check_entail_wit_1_5; intros; c141_or. Qed.

Lemma proof_of_p141_file_name_check_entail_wit_2_1 : p141_file_name_check_entail_wit_2_1.
Proof. unfold p141_file_name_check_entail_wit_2_1; intros; c141_or. Qed.

Lemma proof_of_p141_file_name_check_entail_wit_2_2 : p141_file_name_check_entail_wit_2_2.
Proof. unfold p141_file_name_check_entail_wit_2_2; intros; c141_or. Qed.

Lemma proof_of_p141_file_name_check_entail_wit_2_3 : p141_file_name_check_entail_wit_2_3.
Proof. unfold p141_file_name_check_entail_wit_2_3; intros; c141_or. Qed.

Lemma proof_of_p141_file_name_check_entail_wit_2_4 : p141_file_name_check_entail_wit_2_4.
Proof. unfold p141_file_name_check_entail_wit_2_4; intros; c141_or. Qed.

Lemma proof_of_p141_file_name_check_entail_wit_2_5 : p141_file_name_check_entail_wit_2_5.
Proof. unfold p141_file_name_check_entail_wit_2_5; intros; c141_or. Qed.

Lemma proof_of_p141_file_name_check_entail_wit_2_6 : p141_file_name_check_entail_wit_2_6.
Proof. unfold p141_file_name_check_entail_wit_2_6; intros; c141_or. Qed.

Lemma proof_of_p141_file_name_check_entail_wit_2_7 : p141_file_name_check_entail_wit_2_7.
Proof. unfold p141_file_name_check_entail_wit_2_7; intros; c141_or. Qed.

Lemma proof_of_p141_file_name_check_entail_wit_2_8 : p141_file_name_check_entail_wit_2_8.
Proof. unfold p141_file_name_check_entail_wit_2_8; intros; c141_or. Qed.

Lemma proof_of_p141_file_name_check_entail_wit_2_9 : p141_file_name_check_entail_wit_2_9.
Proof. unfold p141_file_name_check_entail_wit_2_9; intros; c141_or. Qed.

Lemma proof_of_p141_file_name_check_entail_wit_2_10 : p141_file_name_check_entail_wit_2_10.
Proof. unfold p141_file_name_check_entail_wit_2_10; intros; c141_or. Qed.

Lemma proof_of_p141_file_name_check_entail_wit_2_11 : p141_file_name_check_entail_wit_2_11.
Proof. unfold p141_file_name_check_entail_wit_2_11; intros; c141_or. Qed.

Lemma proof_of_p141_file_name_check_entail_wit_4 : p141_file_name_check_entail_wit_4.
Proof.
  unfold p141_file_name_check_entail_wit_4.
  intros.
  c141_prep.
  rewrite digit_count_upto_0.
  rewrite dot_count_upto_0.
  entailer!.
Qed.

Lemma proof_of_p141_file_name_check_entail_wit_5_1 : p141_file_name_check_entail_wit_5_1.
Proof.
  unfold p141_file_name_check_entail_wit_5_1.
  intros.
  c141_prep.
  rewrite digit_count_upto_step_miss by (unfold is_digit; lia).
  rewrite dot_count_upto_step_hit by lia.
  entailer!.
Qed.

Lemma proof_of_p141_file_name_check_entail_wit_5_2 : p141_file_name_check_entail_wit_5_2.
Proof.
  unfold p141_file_name_check_entail_wit_5_2.
  intros.
  c141_prep.
  rewrite digit_count_upto_step_miss by (unfold is_digit; lia).
  rewrite dot_count_upto_step_miss by lia.
  entailer!.
Qed.

Lemma proof_of_p141_file_name_check_entail_wit_5_3 : p141_file_name_check_entail_wit_5_3.
Proof.
  unfold p141_file_name_check_entail_wit_5_3.
  intros.
  c141_prep.
  rewrite digit_count_upto_step_miss by (unfold is_digit; lia).
  rewrite dot_count_upto_step_miss by lia.
  entailer!.
Qed.

Lemma proof_of_p141_file_name_check_entail_wit_5_4 : p141_file_name_check_entail_wit_5_4.
Proof.
  unfold p141_file_name_check_entail_wit_5_4.
  intros.
  c141_prep.
  rewrite digit_count_upto_step_hit by (unfold is_digit; lia).
  rewrite dot_count_upto_step_miss by lia.
  entailer!.
Qed.

Lemma proof_of_p141_file_name_check_entail_wit_6 : p141_file_name_check_entail_wit_6.
Proof.
  unfold p141_file_name_check_entail_wit_6.
  intros.
  c141_prep.
  assert (i = Zlength l) by lia.
  subst i.
  unfold file_name_checks.
  entailer!.
Qed.

Lemma proof_of_p141_file_name_check_return_wit_1 : p141_file_name_check_return_wit_1.
Proof.
  unfold p141_file_name_check_return_wit_1.
  intros.
  c141_prep.
  entailer!.
  apply problem_141_spec_yes.
  assumption.
Qed.

Lemma proof_of_p141_file_name_check_return_wit_2 : p141_file_name_check_return_wit_2.
Proof.
  unfold p141_file_name_check_return_wit_2.
  intros.
  c141_prep.
  assert (i = Zlength l) by lia.
  subst i.
  entailer!.
  apply problem_141_spec_no_dot_ne.
  lia.
Qed.

Lemma proof_of_p141_file_name_check_return_wit_3 : p141_file_name_check_return_wit_3.
Proof.
  unfold p141_file_name_check_return_wit_3.
  intros.
  c141_prep.
  assert (i = Zlength l) by lia.
  subst i.
  entailer!.
  apply problem_141_spec_no_digit_gt.
  lia.
Qed.

Lemma proof_of_p141_file_name_check_return_wit_4 : p141_file_name_check_return_wit_4.
Proof.
  unfold p141_file_name_check_return_wit_4.
  intros.
  c141_prep.
  entailer!.
  apply problem_141_spec_no_not_suffix.
  assumption.
Qed.

Lemma proof_of_p141_file_name_check_return_wit_5 : p141_file_name_check_return_wit_5.
Proof.
  unfold p141_file_name_check_return_wit_5.
  intros.
  c141_prep.
  entailer!.
  apply problem_141_spec_no_not_alpha.
  assumption.
Qed.

Lemma proof_of_p141_file_name_check_return_wit_6 : p141_file_name_check_return_wit_6.
Proof.
  unfold p141_file_name_check_return_wit_6.
  intros.
  c141_prep.
  entailer!.
  apply problem_141_spec_no_len_lt.
  lia.
Qed.

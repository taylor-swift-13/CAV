Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
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
Import naive_C_Rules.
Require Import p141_file_name_check.
Local Open Scope sac.

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

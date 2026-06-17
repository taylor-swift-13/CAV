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
From SimpleC.EE.CAV.ground_truth_p056_correct_bracketing Require Import p056_correct_bracketing_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
From AUXLib Require Import ListLib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p056_correct_bracketing.
Local Open Scope sac.

Ltac c56_pre :=
  pre_process;
  repeat rewrite app_Znth1 in * by lia.

Lemma proof_of_p056_correct_bracketing_entail_wit_1 : p056_correct_bracketing_entail_wit_1.
Proof.
  unfold p056_correct_bracketing_entail_wit_1.
  intros.
  c56_pre.
  subst retval.
  rewrite angle_level_upto_0.
  entailer!.
  apply angle_nonnegative_prefix_0.
Qed.

Lemma proof_of_p056_correct_bracketing_entail_wit_2_1 : p056_correct_bracketing_entail_wit_2_1.
Proof.
  unfold p056_correct_bracketing_entail_wit_2_1.
  intros.
  c56_pre.
  match goal with
  | Hpre : problem_56_pre l |- _ =>
      destruct (problem_56_pre_char l i Hpre ltac:(lia)) as [Hopen | Hclose];
      congruence
  end.
Qed.

Lemma proof_of_p056_correct_bracketing_entail_wit_2_2 : p056_correct_bracketing_entail_wit_2_2.
Proof.
  unfold p056_correct_bracketing_entail_wit_2_2.
  intros.
  c56_pre.
  assert (Hstep : angle_level_upto (i + 1) l = level - 1).
  { rewrite angle_level_upto_step_close by lia. lia. }
  entailer!.
  eapply angle_nonnegative_prefix_step; eauto; lia.
Qed.

Lemma proof_of_p056_correct_bracketing_entail_wit_2_3 : p056_correct_bracketing_entail_wit_2_3.
Proof.
  unfold p056_correct_bracketing_entail_wit_2_3.
  intros.
  c56_pre.
  assert (Hstep : angle_level_upto (i + 1) l = level + 1).
  { rewrite angle_level_upto_step_open by lia. lia. }
  entailer!.
  eapply angle_nonnegative_prefix_step; eauto; lia.
Qed.

Lemma proof_of_p056_correct_bracketing_return_wit_1 : p056_correct_bracketing_return_wit_1.
Proof.
  unfold p056_correct_bracketing_return_wit_1.
  intros.
  c56_pre.
  subst level.
  assert (i = len) by lia.
  subst i.
  entailer!; try (eapply problem_56_pre_nonzero; eauto; lia).
  eapply problem_56_spec_true; eauto.
  - match goal with
    | Hlen : Zlength l = len,
      Hlevel : 0 = angle_level_upto len l |- _ =>
        rewrite Hlen; symmetry; exact Hlevel
    end.
  - match goal with
    | Hlen : Zlength l = len,
      Hprefix : angle_nonnegative_prefix len l |- _ =>
        rewrite Hlen; exact Hprefix
    end.
Qed.

Lemma proof_of_p056_correct_bracketing_return_wit_2 : p056_correct_bracketing_return_wit_2.
Proof.
  unfold p056_correct_bracketing_return_wit_2.
  intros.
  c56_pre.
  assert (i = len) by lia.
  subst i.
  assert (Hfinal_level : angle_level_upto (Zlength l) l = level).
  {
    match goal with
    | Hlen : Zlength l = len,
      Hlevel : level = angle_level_upto len l |- _ =>
        rewrite Hlen; symmetry; exact Hlevel
    end.
  }
  entailer!; try (eapply problem_56_pre_nonzero; eauto; lia).
  eapply problem_56_spec_false_final; eauto.
Qed.

Lemma proof_of_p056_correct_bracketing_return_wit_3 : p056_correct_bracketing_return_wit_3.
Proof.
  unfold p056_correct_bracketing_return_wit_3.
  intros.
  c56_pre.
  entailer!; try (eapply problem_56_pre_nonzero; eauto; lia).
  eapply problem_56_spec_false_negative with (i := i); eauto; try lia.
  rewrite angle_level_upto_step_close by lia.
  lia.
Qed.

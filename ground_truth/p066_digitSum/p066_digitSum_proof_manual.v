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
From SimpleC.EE.CAV.ground_truth_p066_digitSum Require Import p066_digitSum_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
From AUXLib Require Import ListLib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p066_digitSum.
Local Open Scope sac.

Lemma proof_of_p066_digitSum_safety_wit_5 : p066_digitSum_safety_wit_5.
Proof.
  unfold p066_digitSum_safety_wit_5.
  intros.
  pre_process.
  subst sum.
  match goal with
  | Hrange : digit_sum_int_range l |- _ =>
      destruct (Hrange i ltac:(lia) ltac:(lia)) as [_ Hadd]
  end.
  rewrite app_Znth1 by lia.
  entailer!.
Qed.

Lemma proof_of_p066_digitSum_entail_wit_1 : p066_digitSum_entail_wit_1.
Proof.
  unfold p066_digitSum_entail_wit_1.
  intros.
  pre_process.
  subst retval.
  rewrite sum_upper_upto_0.
  entailer!.
Qed.

Lemma proof_of_p066_digitSum_entail_wit_2_1 : p066_digitSum_entail_wit_2_1.
Proof.
  unfold p066_digitSum_entail_wit_2_1.
  intros.
  pre_process.
  subst sum.
  rewrite app_Znth1 in * by lia.
  rewrite sum_upper_upto_step_upper by lia.
  entailer!.
Qed.

Lemma proof_of_p066_digitSum_entail_wit_2_2 : p066_digitSum_entail_wit_2_2.
Proof.
  unfold p066_digitSum_entail_wit_2_2.
  intros.
  pre_process.
  subst sum.
  rewrite app_Znth1 in * by lia.
  rewrite sum_upper_upto_step_not_upper by lia.
  entailer!.
Qed.

Lemma proof_of_p066_digitSum_entail_wit_2_3 : p066_digitSum_entail_wit_2_3.
Proof.
  unfold p066_digitSum_entail_wit_2_3.
  intros.
  pre_process.
  subst sum.
  rewrite app_Znth1 in * by lia.
  rewrite sum_upper_upto_step_not_upper by lia.
  entailer!.
Qed.

Lemma proof_of_p066_digitSum_return_wit_1 : p066_digitSum_return_wit_1.
Proof.
  unfold p066_digitSum_return_wit_1.
  intros.
  pre_process.
  subst sum.
  assert (i = len) by lia.
  subst i.
  entailer!.
  eapply problem_66_spec_intro; eauto.
  rewrite H2.
  reflexivity.
Qed.

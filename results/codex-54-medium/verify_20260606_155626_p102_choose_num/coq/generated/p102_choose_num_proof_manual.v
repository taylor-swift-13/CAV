Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260606_155626_p102_choose_num Require Import p102_choose_num_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p102_choose_num.
Local Open Scope sac.

Lemma proof_of_p102_choose_num_return_wit_1 : p102_choose_num_return_wit_1.
Proof.
  pre_process.
  entailer!.
  pose proof H as Hneq1.
  rewrite (Z.rem_mod_nonneg y_pre 2) in Hneq1 by lia.
  assert (Hy_even : Z.even y_pre = true).
  {
    destruct (Z.even y_pre) eqn:Hev; auto.
    pose proof (Zmod_even y_pre) as Hmod.
    rewrite Hev in Hmod.
    simpl in Hmod.
    exfalso.
    apply Hneq1.
    exact Hmod.
  }
  split.
  - intros _.
    split.
    + exact Hy_even.
    + split; [lia | split; [lia |]].
      intros z' (Hgt & Hle).
      lia.
  - intros Hno.
    exfalso.
    apply Hno.
    exists y_pre.
    repeat split; try lia.
    exact Hy_even.
Qed.

Lemma proof_of_p102_choose_num_return_wit_2 : p102_choose_num_return_wit_2.
Proof.
  pre_process.
  entailer!.
  pose proof H as Hneq1.
  rewrite (Z.rem_mod_nonneg y_pre 2) in Hneq1 by lia.
  assert (Hy_even : Z.even y_pre = true).
  {
    destruct (Z.even y_pre) eqn:Hev; auto.
    pose proof (Zmod_even y_pre) as Hmod.
    rewrite Hev in Hmod.
    simpl in Hmod.
    exfalso.
    apply Hneq1.
    exact Hmod.
  }
  split.
  - intros _.
    split.
    + exact Hy_even.
    + split; [lia | split; [lia |]].
      intros z' (Hgt & Hle).
      lia.
  - intros Hno.
    exfalso.
    apply Hno.
    exists y_pre.
    repeat split; try lia.
    exact Hy_even.
Qed.

Lemma proof_of_p102_choose_num_return_wit_3 : p102_choose_num_return_wit_3.
Proof.
  pre_process.
  entailer!.
  pose proof H as Hodd1.
  rewrite (Z.rem_mod_nonneg y_pre 2) in Hodd1 by lia.
  assert (Hy_odd : Z.odd y_pre = true).
  {
    destruct (Z.odd y_pre) eqn:Hoddb; auto.
    pose proof (Zmod_odd y_pre) as Hmod.
    rewrite Hoddb in Hmod.
    rewrite Hodd1 in Hmod.
    discriminate.
  }
  assert (Hx_lt_y : x_pre < y_pre) by lia.
  split.
  - intros _.
    split.
    + rewrite Z.sub_1_r.
      rewrite Z.even_pred.
      exact Hy_odd.
    + split; [lia | split; [lia |]].
      intros z' (Hgt & Hle).
      assert (z' = y_pre) by lia.
      subst z'.
      rewrite <- Z.negb_odd.
      now rewrite Hy_odd.
  - intros Hno.
    exfalso.
    apply Hno.
    exists (y_pre - 1).
    split; [lia | split; [lia |]].
    rewrite Z.sub_1_r.
    rewrite Z.even_pred.
    exact Hy_odd.
Qed.

Lemma proof_of_p102_choose_num_return_wit_4 : p102_choose_num_return_wit_4.
Proof.
  pre_process.
  entailer!.
  pose proof H as Hodd1.
  rewrite (Z.rem_mod_nonneg y_pre 2) in Hodd1 by lia.
  assert (Hy_odd : Z.odd y_pre = true).
  {
    destruct (Z.odd y_pre) eqn:Hoddb; auto.
    pose proof (Zmod_odd y_pre) as Hmod.
    rewrite Hoddb in Hmod.
    rewrite Hodd1 in Hmod.
    discriminate.
  }
  split.
  - intros (z & Hx & Hy & Hz_even).
    subst y_pre.
    assert (z = x_pre) by lia.
    subst z.
    rewrite <- Z.negb_odd in Hz_even.
    now rewrite Hy_odd in Hz_even.
  - intros _.
    lia.
Qed.

Lemma proof_of_p102_choose_num_return_wit_5 : p102_choose_num_return_wit_5.
Proof.
  pre_process.
  entailer!.
  split.
  - intros (z & Hx & Hy & _).
    lia.
  - intros _.
    lia.
Qed.

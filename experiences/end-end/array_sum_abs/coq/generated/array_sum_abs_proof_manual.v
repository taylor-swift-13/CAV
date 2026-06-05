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
From SimpleC.EE.CAV.verify_20260605_005812v_array_sum_abs Require Import array_sum_abs_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_sum_abs.
Local Open Scope sac.

Lemma sum_abs_app : forall l1 l2,
  sum_abs (l1 ++ l2) = sum_abs l1 + sum_abs l2.
Proof.
  intros l1.
  induction l1 as [| x xs IH]; intros l2.
  - reflexivity.
  - unfold sum_abs in IH |- *. simpl. rewrite IH. lia.
Qed.

Lemma sum_abs_nonneg : forall l,
  0 <= sum_abs l.
Proof.
  intros l.
  unfold sum_abs.
  induction l as [| x xs IH].
  - simpl. lia.
  - simpl. pose proof Z.abs_nonneg x. lia.
Qed.

Lemma sum_abs_singleton_nonneg : forall x,
  0 <= x ->
  sum_abs (x :: nil) = x.
Proof.
  intros x Hx.
  unfold sum_abs.
  simpl.
  rewrite Z.abs_eq by lia.
  lia.
Qed.

Lemma sum_abs_singleton_neg : forall x,
  x < 0 ->
  sum_abs (x :: nil) = -x.
Proof.
  intros x Hx.
  unfold sum_abs.
  simpl.
  rewrite Z.abs_neq by lia.
  lia.
Qed.

Lemma sum_abs_prefix_le : forall l i,
  0 <= i <= Zlength l ->
  sum_abs (sublist 0 i l) <= sum_abs l.
Proof.
  intros l i Hi.
  assert (Hsplit: sublist 0 (Zlength l) l = sublist 0 i l ++ sublist i (Zlength l) l).
  {
    rewrite sublist_split with (mid := i); try lia.
    reflexivity.
  }
  rewrite sublist_self in Hsplit by reflexivity.
  rewrite Hsplit at 2.
  rewrite sum_abs_app.
  pose proof sum_abs_nonneg (sublist i (Zlength l) l) as Hnn.
  lia.
Qed.

Lemma sum_abs_sublist_succ_nonneg : forall l i,
  0 <= i < Zlength l ->
  0 <= Znth i l 0 ->
  sum_abs (sublist 0 (i + 1) l) = sum_abs (sublist 0 i l) + Znth i l 0.
Proof.
  intros l i Hi Hz.
  assert (Hsplit: sublist 0 (i + 1) l = sublist 0 i l ++ sublist i (i + 1) l).
  {
    rewrite sublist_split with (mid := i); try lia.
    reflexivity.
  }
  rewrite Hsplit.
  rewrite sublist_single with (d := 0) by lia.
  rewrite sum_abs_app.
  rewrite sum_abs_singleton_nonneg by lia.
  lia.
Qed.

Lemma sum_abs_sublist_succ_neg : forall l i,
  0 <= i < Zlength l ->
  Znth i l 0 < 0 ->
  sum_abs (sublist 0 (i + 1) l) = sum_abs (sublist 0 i l) + (-(Znth i l 0)).
Proof.
  intros l i Hi Hz.
  assert (Hsplit: sublist 0 (i + 1) l = sublist 0 i l ++ sublist i (i + 1) l).
  {
    rewrite sublist_split with (mid := i); try lia.
    reflexivity.
  }
  rewrite Hsplit.
  rewrite sublist_single with (d := 0) by lia.
  rewrite sum_abs_app.
  rewrite sum_abs_singleton_neg by lia.
  lia.
Qed.

Lemma proof_of_array_sum_abs_safety_wit_4 : array_sum_abs_safety_wit_4.
Proof.
  pre_process.
  entailer!.
  assert (Hlb : -2147483647 <= Znth i l 0).
  {
    apply H4.
    lia.
  }
  lia.
Qed.

Lemma proof_of_array_sum_abs_safety_wit_5 : array_sum_abs_safety_wit_5.
Proof.
  pre_process.
  entailer!.
  - assert (Hstep: sum + Znth i l 0 = sum_abs (sublist 0 (i + 1) l)).
    {
      rewrite H7.
      symmetry.
      apply sum_abs_sublist_succ_nonneg; lia.
    }
    rewrite Hstep.
    pose proof sum_abs_nonneg (sublist 0 (i + 1) l).
    lia.
  - assert (Hstep: sum + Znth i l 0 = sum_abs (sublist 0 (i + 1) l)).
    {
      rewrite H7.
      symmetry.
      apply sum_abs_sublist_succ_nonneg; lia.
    }
    rewrite Hstep.
    eapply Z.le_trans.
    2: exact H6.
    apply sum_abs_prefix_le.
    lia.
Qed.

Lemma proof_of_array_sum_abs_safety_wit_6 : array_sum_abs_safety_wit_6.
Proof.
  pre_process.
  entailer!.
  - assert (Hstep: sum + - Znth i l 0 = sum_abs (sublist 0 (i + 1) l)).
    {
      rewrite H7.
      symmetry.
      apply sum_abs_sublist_succ_neg; lia.
    }
    rewrite Hstep.
    pose proof sum_abs_nonneg (sublist 0 (i + 1) l).
    lia.
  - assert (Hstep: sum + - Znth i l 0 = sum_abs (sublist 0 (i + 1) l)).
    {
      rewrite H7.
      symmetry.
      apply sum_abs_sublist_succ_neg; lia.
    }
    rewrite Hstep.
    eapply Z.le_trans.
    2: exact H6.
    apply sum_abs_prefix_le.
    lia.
Qed.

Lemma proof_of_array_sum_abs_entail_wit_1 : array_sum_abs_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_array_sum_abs_entail_wit_2_1 : array_sum_abs_entail_wit_2_1.
Proof.
  pre_process.
  entailer!.
  assert (Hstep: sum + Znth i l 0 = sum_abs (sublist 0 (i + 1) l)) by
    (rewrite H7; symmetry; apply sum_abs_sublist_succ_nonneg; lia).
  exact Hstep.
Qed.

Lemma proof_of_array_sum_abs_entail_wit_2_2 : array_sum_abs_entail_wit_2_2.
Proof.
  pre_process.
  entailer!.
  assert (Hstep: sum + - Znth i l 0 = sum_abs (sublist 0 (i + 1) l)) by
    (rewrite H7; symmetry; apply sum_abs_sublist_succ_neg; lia).
  exact Hstep.
Qed.

Lemma proof_of_array_sum_abs_return_wit_1 : array_sum_abs_return_wit_1.
Proof.
  pre_process.
  entailer!.
  assert (i = n_pre) by lia.
  subst i.
  rewrite sublist_self in H6 by auto.
  exact H6.
Qed.

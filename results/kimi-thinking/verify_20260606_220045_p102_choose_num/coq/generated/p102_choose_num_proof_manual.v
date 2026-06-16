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
From SimpleC.EE.CAV.verify_20260606_220045_p102_choose_num Require Import p102_choose_num_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p102_choose_num.
Local Open Scope sac.

Lemma rem2_0_even_true : forall a, 0 <= a -> Z.rem a 2 = 0 -> Z.even a = true.
Proof.
  intros a Ha Hrem.
  rewrite Z.rem_mod_nonneg in Hrem; try lia.
  pose proof (Zmod_even a) as Heq.
  assert (H: a mod 2 = 0) by auto.
  rewrite H in Heq.
  destruct (Z.even a); [reflexivity | discriminate Heq].
Qed.

(* Helper: Z.rem a 2 = 1 implies Z.even a = false, for a >= 0 *)
Lemma rem2_1_even_false : forall a, 0 <= a -> Z.rem a 2 = 1 -> Z.even a = false.
Proof.
  intros a Ha Hrem.
  rewrite Z.rem_mod_nonneg in Hrem; try lia.
  pose proof (Zmod_even a) as Heq.
  assert (H: a mod 2 = 1) by auto.
  rewrite H in Heq.
  destruct (Z.even a); [discriminate Heq | reflexivity].
Qed.

(* Helper: Z.rem a 2 = 1 implies Z.even (a - 1) = true, for a >= 0 *)
Lemma rem2_1_even_pred_true : forall a, 0 <= a -> Z.rem a 2 = 1 -> Z.even (a - 1) = true.
Proof.
  intros a Ha Hrem.
  pose proof (rem2_1_even_false a Ha Hrem) as Heven_false.
  replace (a - 1) with (Z.pred a) by lia.
  rewrite Z.even_pred.
  rewrite <- Z.negb_even.
  rewrite Heven_false.
  auto.
Qed.

(* Helper: Z.rem a 2 <> 1 and a >= 0 implies Z.rem a 2 = 0 *)
Lemma rem2_not1_eq0 : forall a, 0 <= a -> Z.rem a 2 <> 1 -> Z.rem a 2 = 0.
Proof.
  intros a Ha Hne.
  rewrite Z.rem_mod_nonneg in *; try lia.
  pose proof (Z.mod_pos_bound a 2 ltac:(lia)) as Hb.
  assert (a mod 2 = 0 \/ a mod 2 = 1) by lia.
  destruct H; [assumption | congruence].
Qed.

Lemma proof_of_p102_choose_num_return_wit_1 : p102_choose_num_return_wit_1.
Proof.
  pre_process.
  entailer!.
  unfold problem_102_spec.
  split.
  - intros [z [Hz1 [Hz2 Hze]]].
    split; [ | split; [ | split] ].
    + apply rem2_0_even_true; try lia.
      apply rem2_not1_eq0; lia.
    + lia.
    + lia.
    + intros z' [Hz'1 Hz'2].
      lia.
  - intros Hnoeven.
    exfalso.
    apply Hnoeven.
    exists y_pre.
    split; [lia | split; [lia | ]].
    apply rem2_0_even_true; try lia.
    apply rem2_not1_eq0; lia.
Qed.

Lemma proof_of_p102_choose_num_return_wit_2 : p102_choose_num_return_wit_2.
Proof.
  pre_process.
  entailer!.
  unfold problem_102_spec.
  split.
  - intros [z [Hz1 [Hz2 Hze]]].
    split; [ | split; [ | split] ].
    + apply rem2_0_even_true; try lia.
      apply rem2_not1_eq0; lia.
    + lia.
    + lia.
    + intros z' [Hz'1 Hz'2].
      lia.
  - intros Hnoeven.
    exfalso.
    apply Hnoeven.
    exists y_pre.
    split; [lia | split; [lia | ]].
    apply rem2_0_even_true; try lia.
    apply rem2_not1_eq0; lia.
Qed.

Lemma proof_of_p102_choose_num_return_wit_3 : p102_choose_num_return_wit_3.
Proof.
  pre_process.
  entailer!.
  unfold problem_102_spec.
  split.
  - intros [z [Hz1 [Hz2 Hze]]].
    split; [ | split; [ | split] ].
    + assert (Z.even (y_pre - 1) = true).
      { apply rem2_1_even_pred_true; lia. }
      auto.
    + lia.
    + lia.
    + intros z' [Hz'1 Hz'2].
      assert (z' = y_pre) by lia.
      subst z'.
      apply rem2_1_even_false; lia.
  - intros Hnoeven.
    exfalso.
    apply Hnoeven.
    exists (y_pre - 1).
    split; [lia | split; [lia | ]].
    assert (Z.even (y_pre - 1) = true).
    { apply rem2_1_even_pred_true; lia. }
    auto.
Qed.

Lemma proof_of_p102_choose_num_return_wit_4 : p102_choose_num_return_wit_4.
Proof.
  pre_process.
  entailer!.
  unfold problem_102_spec.
  split.
  - intros [z [Hz1 [Hz2 Hze]]].
    assert (z = y_pre) by lia.
    subst z.
    pose proof (rem2_1_even_false y_pre ltac:(lia) H).
    congruence.
  - intros. reflexivity.
Qed.

Lemma proof_of_p102_choose_num_return_wit_5 : p102_choose_num_return_wit_5.
Proof.
  pre_process.
  entailer!.
  unfold problem_102_spec.
  split.
  - intros [z [Hz1 [Hz2 Hze]]].
    lia.
  - intros. reflexivity.
Qed.

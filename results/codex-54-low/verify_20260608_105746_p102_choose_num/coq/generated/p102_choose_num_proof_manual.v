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
From SimpleC.EE.CAV.verify_20260608_105746_p102_choose_num Require Import p102_choose_num_goal.
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
  unfold problem_102_spec.
  entailer!.
  - intros _.
    split.
    { apply Z.even_spec.
      destruct (Z.Even_or_Odd y_pre) as [Heven | Hodd].
      - exact Heven.
      - exfalso.
        destruct Hodd as [k Hk].
        assert (Hy1 : y_pre % 2 = 1).
        { rewrite Z.rem_mod_nonneg by lia.
          rewrite Hk.
          rewrite Z.add_mod by lia.
          rewrite Z.mul_mod by lia.
          rewrite Z.mod_same by lia.
          rewrite Z.mod_0_l by lia.
          cbn.
          reflexivity. }
        apply H; exact Hy1. }
    repeat split; lia.
  - intros Hcontra.
    exfalso.
    apply Hcontra.
    exists y_pre.
    repeat split; try lia.
    apply Z.even_spec.
    destruct (Z.Even_or_Odd y_pre) as [Heven | Hodd].
    * exact Heven.
    * exfalso.
      destruct Hodd as [k Hk].
      assert (Hy1 : y_pre % 2 = 1).
      { rewrite Z.rem_mod_nonneg by lia.
        rewrite Hk.
        rewrite Z.add_mod by lia.
        rewrite Z.mul_mod by lia.
        rewrite Z.mod_same by lia.
        rewrite Z.mod_0_l by lia.
        cbn.
        reflexivity. }
      exfalso; apply H; exact Hy1.
Qed.

Lemma proof_of_p102_choose_num_return_wit_2 : p102_choose_num_return_wit_2.
Proof.
  pre_process.
  unfold problem_102_spec.
  entailer!.
  - intros _.
    split.
    { apply Z.even_spec.
      destruct (Z.Even_or_Odd y_pre) as [Heven | Hodd].
      - exact Heven.
      - exfalso.
        destruct Hodd as [k Hk].
        assert (Hy1 : y_pre % 2 = 1).
        { rewrite Z.rem_mod_nonneg by lia.
          rewrite Hk.
          rewrite Z.add_mod by lia.
          rewrite Z.mul_mod by lia.
          rewrite Z.mod_same by lia.
          rewrite Z.mod_0_l by lia.
          cbn.
          reflexivity. }
        apply H; exact Hy1. }
    repeat split; lia.
  - intros Hcontra.
    exfalso.
    apply Hcontra.
    exists y_pre.
    repeat split; try lia.
    apply Z.even_spec.
    destruct (Z.Even_or_Odd y_pre) as [Heven | Hodd].
    * exact Heven.
    * exfalso.
      destruct Hodd as [k Hk].
      assert (Hy1 : y_pre % 2 = 1).
      { rewrite Z.rem_mod_nonneg by lia.
        rewrite Hk.
        rewrite Z.add_mod by lia.
        rewrite Z.mul_mod by lia.
        rewrite Z.mod_same by lia.
        rewrite Z.mod_0_l by lia.
        cbn.
        reflexivity. }
      exfalso; apply H; exact Hy1.
Qed.

Lemma proof_of_p102_choose_num_return_wit_3 : p102_choose_num_return_wit_3.
Proof.
  pre_process.
  unfold problem_102_spec.
  entailer!.
  - intros _.
    split.
    + apply Z.even_spec.
      destruct (Z.Even_or_Odd y_pre) as [Heven | Hodd].
      * exfalso.
        destruct Heven as [k Hk].
        assert (Hy0 : y_pre % 2 = 0).
        { rewrite Z.rem_mod_nonneg by lia.
          rewrite Hk.
          rewrite Z.mul_mod by lia.
          rewrite Z.mod_same by lia.
          rewrite Z.mod_0_l by lia.
          reflexivity. }
        rewrite Hy0 in H. discriminate.
      * destruct Hodd as [k Hk].
        exists k.
        lia.
    + repeat split; try lia.
      intros z' [? ?].
      assert (z' = y_pre) by lia.
      subst z'.
      destruct (Z.even y_pre) eqn:Hev.
      * apply Z.even_spec in Hev.
        destruct Hev as [k Hk].
        assert (Hy0 : y_pre % 2 = 0).
        { rewrite Z.rem_mod_nonneg by lia.
          rewrite Hk.
          rewrite Z.mul_mod by lia.
          rewrite Z.mod_same by lia.
          rewrite Z.mod_0_l by lia.
          reflexivity. }
        rewrite Hy0 in H.
        discriminate.
      * reflexivity.
  - intros Hnone.
    exfalso.
    apply Hnone.
    exists (y_pre - 1).
    repeat split; try lia.
    apply Z.even_spec.
    destruct (Z.Even_or_Odd y_pre) as [Heven | Hodd].
    * exfalso.
      destruct Heven as [k Hk].
      assert (Hy0 : y_pre % 2 = 0).
      { rewrite Z.rem_mod_nonneg by lia.
        rewrite Hk.
        rewrite Z.mul_mod by lia.
        rewrite Z.mod_same by lia.
        rewrite Z.mod_0_l by lia.
        reflexivity. }
      rewrite Hy0 in H. discriminate.
    * destruct Hodd as [k Hk].
      exists k.
      lia.
Qed.

Lemma proof_of_p102_choose_num_return_wit_4 : p102_choose_num_return_wit_4.
Proof.
  pre_process.
  unfold problem_102_spec.
  entailer!.
  - intros Hex.
    destruct Hex as [z [? [? Heven]]].
    assert (z = y_pre) by lia.
    subst z.
    apply Z.even_spec in Heven.
    destruct Heven as [k Hk].
    assert (Hy0 : y_pre % 2 = 0).
    { rewrite Z.rem_mod_nonneg by lia.
      rewrite Hk.
      rewrite Z.mul_mod by lia.
      rewrite Z.mod_same by lia.
      rewrite Z.mod_0_l by lia.
      reflexivity. }
    rewrite Hy0 in H.
    discriminate.
Qed.

Lemma proof_of_p102_choose_num_return_wit_5 : p102_choose_num_return_wit_5.
Proof.
  pre_process.
  unfold problem_102_spec.
  entailer!.
  - intros Hex.
    destruct Hex as [z [? [? _]]].
    lia.
Qed.

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
From Verify.Annotated Require Import p009_rolling_max_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p009_rolling_max.
Local Open Scope sac.
Require Import Coq.micromega.Lia.

Lemma rolling_max_f_Zlength :
  forall mx l,
    Zlength (rolling_max_f mx l) = Zlength l.
Proof.
  intros mx l.
  revert mx.
  induction l as [| x xs IH]; intros mx; simpl.
  - reflexivity.
  - rewrite !Zlength_cons. rewrite IH. reflexivity.
Qed.

Lemma running_max_val_ge_seed :
  forall mx l,
    mx <= running_max_val mx l.
Proof.
  intros mx l.
  revert mx.
  induction l as [| x xs IH]; intros mx; simpl; [lia |].
  eapply Z.le_trans.
  - apply Z.le_max_l.
  - apply IH.
Qed.

Lemma running_max_val_upper_bound :
  forall mx l j,
    0 <= j < Zlength l ->
    Znth j l 0 <= running_max_val mx l.
Proof.
  intros mx l.
  revert mx.
  induction l as [| x xs IH]; intros mx j Hj.
  - rewrite Zlength_nil in Hj. lia.
  - rewrite Zlength_cons in Hj.
    destruct (Z.eq_dec j 0) as [-> | Hneq].
    + simpl.
      eapply Z.le_trans.
      * apply Z.le_max_r.
      * apply running_max_val_ge_seed.
    + rewrite Znth_cons by lia.
      specialize (IH (Z.max mx x) (j - 1)).
      assert (0 <= j - 1 < Zlength xs) by lia.
      specialize (IH H).
      exact IH.
Qed.

Lemma running_max_val_app_single :
  forall mx l x,
    running_max_val mx (l ++ x :: nil) = Z.max (running_max_val mx l) x.
Proof.
  intros mx l.
  revert mx.
  induction l as [| a l IH]; intros mx x; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma rolling_max_f_app_single :
  forall mx l x,
    rolling_max_f mx (l ++ x :: nil) =
    rolling_max_f mx l ++ running_max_val mx (l ++ x :: nil) :: nil.
Proof.
  intros mx l.
  revert mx.
  induction l as [| a l IH]; intros mx x; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma rolling_max_f_prefix :
  forall mx l n,
    0 <= n <= Zlength l ->
    sublist 0 n (rolling_max_f mx l) = rolling_max_f mx (sublist 0 n l).
Proof.
  intros mx l.
  revert mx.
  induction l as [| a l IH]; intros mx n Hn.
  - assert (n = 0) by (rewrite Zlength_nil in Hn; lia).
    subst n. reflexivity.
  - destruct (Z.eq_dec n 0) as [-> | Hnz].
    + reflexivity.
    + assert (0 < n) by lia.
      assert (Hs_in :
        sublist 0 n (a :: l) = a :: sublist 0 (n - 1) l).
      {
        unfold sublist.
        replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by lia.
        simpl. reflexivity.
      }
      assert (Hs_out :
        sublist 0 n (Z.max mx a :: rolling_max_f (Z.max mx a) l) =
        Z.max mx a :: sublist 0 (n - 1) (rolling_max_f (Z.max mx a) l)).
      {
        unfold sublist.
        replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by lia.
        simpl. reflexivity.
      }
      simpl.
      rewrite Hs_in, Hs_out.
      simpl.
      f_equal.
      apply IH.
      rewrite Zlength_cons in Hn. lia.
Qed.

Lemma list_int_range_Znth :
  forall l i,
    list_int_range l ->
    0 <= i < Zlength l ->
    INT_MIN <= Znth i l 0 <= INT_MAX.
Proof.
  intros l i Hrange Hi.
  unfold list_int_range in Hrange.
  unfold Znth.
  rewrite Zlength_correct in Hi.
  specialize (Hrange (Z.to_nat i)).
  assert ((Z.to_nat i < length l)%nat) by lia.
  specialize (Hrange H).
  exact Hrange.
Qed.

Lemma running_max_val_witness_or_seed :
  forall mx l,
    exists j,
      -1 <= j < Zlength l /\
      ((j = -1 /\ running_max_val mx l = mx) \/
       (0 <= j /\ Znth j l 0 = running_max_val mx l)).
Proof.
  intros mx l.
  revert mx.
  induction l as [| a l IH]; intros mx.
  - exists (-1). split.
    + rewrite Zlength_nil. lia.
    + left. split; reflexivity.
  - simpl.
    destruct (IH (Z.max mx a)) as [j [Hj [Hseed | Helt]]].
    + destruct Hseed as [Hjneg Hrm].
      subst j.
      destruct (Z_le_gt_dec a mx) as [Hle | Hgt].
      * exists (-1). split.
        { rewrite Zlength_cons. lia. }
        left. split; [lia |].
        rewrite Hrm. rewrite Z.max_l by lia. reflexivity.
      * exists 0. split.
        { rewrite Zlength_cons. lia. }
        right. split; [lia |].
        rewrite Hrm. simpl. rewrite Z.max_r by lia. reflexivity.
    + destruct Helt as [Hj0 Hz].
      exists (j + 1). split.
      * rewrite Zlength_cons in *. lia.
      * right. split; [lia |].
        rewrite Znth_cons by lia.
        replace (j + 1 - 1) with j by lia.
        exact Hz.
Qed.

Lemma running_max_val_witness_from_range :
  forall mx l,
    (forall j, 0 <= j < Zlength l -> mx <= Znth j l 0) ->
    0 < Zlength l ->
    exists j, 0 <= j < Zlength l /\ Znth j l 0 = running_max_val mx l.
Proof.
  intros mx l Hrange Hlen.
  destruct (running_max_val_witness_or_seed mx l) as [j [Hj [Hseed | Helt]]].
  - destruct Hseed as [Hjneg Hrm].
    assert (Hlo : mx <= Znth 0 l 0) by (apply Hrange; lia).
    assert (Hhi : Znth 0 l 0 <= mx).
    { rewrite <- Hrm. apply running_max_val_upper_bound. lia. }
    exists 0. split; [lia |]. lia.
  - destruct Helt as [Hj0 Hz].
    exists j. split; [lia | exact Hz].
Qed.

Lemma rolling_max_f_current_value :
  forall mx l i,
    0 <= i < Zlength l ->
    Znth i (rolling_max_f mx l) 0 =
    running_max_val mx (sublist 0 (i + 1) l).
Proof.
  intros mx l i Hi.
  rewrite <- (@Znth_sublist0 Z 0 i (i + 1) (rolling_max_f mx l)) by lia.
  rewrite rolling_max_f_prefix by lia.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single 0 i l) by lia.
  rewrite rolling_max_f_app_single.
  rewrite app_Znth2 by (rewrite rolling_max_f_Zlength, Zlength_sublist0; lia).
  replace (i - Zlength (rolling_max_f mx (sublist 0 i l))) with 0
    by (rewrite rolling_max_f_Zlength, Zlength_sublist0; lia).
  simpl.
  replace (running_max_val mx (sublist 0 (i + 1) l))
    with (running_max_val mx (sublist 0 i l ++ Znth i l 0 :: nil)).
  - reflexivity.
  - rewrite (sublist_split 0 (i + 1) i l) by lia.
    rewrite (sublist_single 0 i l) by lia.
    reflexivity.
Qed.

Lemma problem_9_spec_of_rolling_max :
  forall lv,
    list_int_range lv ->
    problem_9_spec lv (rolling_max_f INT_MIN lv).
Proof.
  intros lv Hrange.
  split.
  - apply rolling_max_f_Zlength.
  - intros i Hi.
    assert (Hi_lv : 0 <= i < Zlength lv)
      by (rewrite <- (rolling_max_f_Zlength INT_MIN lv); exact Hi).
    rewrite (rolling_max_f_current_value INT_MIN lv i Hi_lv).
    split.
    + intros j Hj.
      rewrite <- (@Znth_sublist0 Z 0 j (i + 1) lv) by lia.
      pose proof (running_max_val_upper_bound INT_MIN (sublist 0 (i + 1) lv) j) as Hbound.
      assert (0 <= j < Zlength (sublist 0 (i + 1) lv)) by (rewrite Zlength_sublist0; lia).
      specialize (Hbound H).
      exact Hbound.
    + assert (Hpref_range :
          forall j, 0 <= j < Zlength (sublist 0 (i + 1) lv) ->
            INT_MIN <= Znth j (sublist 0 (i + 1) lv) 0).
      {
        intros j Hj.
        assert (Hj' : 0 <= j < i + 1).
        { rewrite Zlength_sublist0 in Hj by lia. lia. }
        rewrite (@Znth_sublist0 Z 0 j (i + 1) lv) by exact Hj'.
        destruct (list_int_range_Znth lv j Hrange) as [Hlo _].
        - lia.
        - exact Hlo.
      }
      destruct (running_max_val_witness_from_range INT_MIN (sublist 0 (i + 1) lv) Hpref_range) as [j [Hj Hz]].
      { rewrite Zlength_sublist0 by lia. lia. }
      assert (Hj_i : 0 <= j <= i).
      { rewrite Zlength_sublist0 in Hj by lia. lia. }
      exists j. split.
      * exact Hj_i.
      * assert (Hj' : 0 <= j < i + 1).
        { rewrite Zlength_sublist0 in Hj by lia. lia. }
        rewrite (@Znth_sublist0 Z 0 j (i + 1) lv) in Hz by exact Hj'.
        exact Hz.
Qed.

Lemma proof_of_p009_rolling_max_entail_wit_1 : p009_rolling_max_entail_wit_1.
Proof.
  pre_process.
  subst.
  Right.
  Exists (@nil Z).
  entailer!.
  simpl.
  assert (Hsplit :
    IntArray.undef_full out0 numbers_size0
    |-- IntArray.undef_seg out0 0 0 ** IntArray.undef_seg out0 0 numbers_size0).
  { apply IntArray.undef_full_split_to_undef_seg. lia. }
  sep_apply Hsplit.
  rewrite (IntArray.undef_seg_empty out0 0).
  rewrite (IntArray.seg_empty out0 0 0).
  entailer!.
Qed.

Lemma proof_of_p009_rolling_max_entail_wit_2_1 : p009_rolling_max_entail_wit_2_1.
Proof.
  pre_process.
  Left.
  Exists (out_prefix_2 ++ cur_max :: nil).
  prop_apply (IntArray.full_Zlength numbers0 numbers_size0 lv).
  Intros.
  split_pure_spatial.
  - cancel (IntArray.full numbers0 numbers_size0 lv).
    cancel (IntArray.seg out0 0 (i + 1) (out_prefix_2 ++ cur_max :: nil)).
    cancel (IntArray.undef_seg out0 (i + 1) out_size0).
  - split_pures; dump_pre_spatial; try lia.
    + exact H5.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil, H8. lia.
    + rewrite H9.
      rewrite (sublist_split 0 (i + 1) i lv) by (rewrite H12; lia).
      rewrite (sublist_single 0 i lv) by (rewrite H12; lia).
      rewrite rolling_max_f_app_single.
      rewrite H11.
      rewrite running_max_val_app_single.
      rewrite Z.max_l by lia.
      reflexivity.
    + rewrite H11.
      rewrite (sublist_split 0 (i + 1) i lv) by (rewrite H12; lia).
      rewrite (sublist_single 0 i lv) by (rewrite H12; lia).
      rewrite running_max_val_app_single.
      rewrite Z.max_l by lia.
      reflexivity.
Qed.

Lemma proof_of_p009_rolling_max_entail_wit_2_2 : p009_rolling_max_entail_wit_2_2.
Proof.
  pre_process.
  assert (Hz : Znth i lv 0 = INT_MIN).
  { subst i. destruct (list_int_range_Znth lv 0 H4) as [Hlo Hhi]; lia. }
  Left.
  Exists (out_prefix_2 ++ cur_max :: nil).
  prop_apply (IntArray.full_Zlength numbers0 numbers_size0 lv).
  Intros.
  split_pure_spatial.
  - cancel (IntArray.full numbers0 numbers_size0 lv).
    cancel (IntArray.seg out0 0 (i + 1) (out_prefix_2 ++ cur_max :: nil)).
    cancel (IntArray.undef_seg out0 (i + 1) out_size0).
  - split_pures; dump_pre_spatial; try lia.
    + exact H5.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil, H8. lia.
    + rewrite H9.
      rewrite (sublist_split 0 (i + 1) i lv) by (rewrite H12; lia).
      rewrite (sublist_single 0 i lv) by (rewrite H12; lia).
      rewrite rolling_max_f_app_single.
      rewrite H11, Hz.
      rewrite running_max_val_app_single.
      rewrite Z.max_l by lia.
      reflexivity.
    + rewrite H11.
      rewrite (sublist_split 0 (i + 1) i lv) by (rewrite H12; lia).
      rewrite (sublist_single 0 i lv) by (rewrite H12; lia).
      rewrite running_max_val_app_single.
      rewrite Hz.
      rewrite Z.max_l by lia.
      reflexivity.
Qed.

Lemma proof_of_p009_rolling_max_entail_wit_2_3 : p009_rolling_max_entail_wit_2_3.
Proof.
  pre_process.
  Left.
  Exists (out_prefix_2 ++ Znth i lv 0 :: nil).
  prop_apply (IntArray.full_Zlength numbers0 numbers_size0 lv).
  Intros.
  split_pure_spatial.
  - cancel (IntArray.full numbers0 numbers_size0 lv).
    cancel (IntArray.seg out0 0 (i + 1) (out_prefix_2 ++ Znth i lv 0 :: nil)).
    cancel (IntArray.undef_seg out0 (i + 1) out_size0).
  - split_pures; dump_pre_spatial; try lia.
    + exact H5.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil, H8. lia.
    + rewrite H9.
      rewrite (sublist_split 0 (i + 1) i lv) by (rewrite H12; lia).
      rewrite (sublist_single 0 i lv) by (rewrite H12; lia).
      rewrite rolling_max_f_app_single.
      rewrite running_max_val_app_single.
      rewrite Z.max_r by lia.
      reflexivity.
    + rewrite (sublist_split 0 (i + 1) i lv) by (rewrite H12; lia).
      rewrite (sublist_single 0 i lv) by (rewrite H12; lia).
      rewrite running_max_val_app_single.
      rewrite Z.max_r by lia.
      reflexivity.
Qed.

Lemma proof_of_p009_rolling_max_entail_wit_2_4 : p009_rolling_max_entail_wit_2_4.
Proof.
  pre_process.
  Left.
  Exists (out_prefix_2 ++ Znth i lv 0 :: nil).
  prop_apply (IntArray.full_Zlength numbers0 numbers_size0 lv).
  Intros.
  split_pure_spatial.
  - cancel (IntArray.full numbers0 numbers_size0 lv).
    cancel (IntArray.seg out0 0 (i + 1) (out_prefix_2 ++ Znth i lv 0 :: nil)).
    cancel (IntArray.undef_seg out0 (i + 1) out_size0).
  - split_pures; dump_pre_spatial; try lia.
    + exact H5.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil, H8. lia.
    + rewrite H9.
      rewrite (sublist_split 0 (i + 1) i lv) by (rewrite H12; lia).
      rewrite (sublist_single 0 i lv) by (rewrite H12; lia).
      rewrite rolling_max_f_app_single.
      rewrite running_max_val_app_single.
      rewrite Z.max_r by lia.
      reflexivity.
    + rewrite (sublist_split 0 (i + 1) i lv) by (rewrite H12; lia).
      rewrite (sublist_single 0 i lv) by (rewrite H12; lia).
      rewrite running_max_val_app_single.
      rewrite Z.max_r by lia.
      reflexivity.
Qed.

Lemma proof_of_p009_rolling_max_return_wit_1 : p009_rolling_max_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = numbers_size0) by lia.
  subst i.
  Exists out_prefix.
  rewrite IntArray.undef_seg_empty.
  sep_apply (IntArray.seg_to_full out0 0 numbers_size0 out_prefix).
  replace (out0 + 0 * sizeof(INT)) with out0 by lia.
  split_pure_spatial.
  - cancel (IntArray.full numbers0 numbers_size0 lv).
    cancel (IntArray.full out0 out_size0 out_prefix).
  - split_pures.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial.
      rewrite H3.
      rewrite sublist_self.
      * apply problem_9_spec_of_rolling_max. exact H1.
      * rewrite Zlength_correct. lia.
Qed.

Lemma proof_of_p009_rolling_max_return_wit_2 : p009_rolling_max_return_wit_2.
Proof.
  pre_process.
  assert (Hn : numbers_size0 = 0) by lia.
  subst numbers_size0.
  Exists out_prefix.
  change (rolling_max_f INT_MIN (sublist 0 0 lv)) with (@nil Z) in H3.
  assert (Hout : out_prefix = nil) by (rewrite H2, H3, Zlength_nil in *; destruct out_prefix; simpl in *; lia || reflexivity).
  subst out_prefix.
  rewrite IntArray.undef_seg_empty.
  sep_apply (IntArray.seg_to_full out0 0 0 (@nil Z)).
  replace (out0 + 0 * sizeof(INT)) with out0 by lia.
  split_pure_spatial.
  - cancel (IntArray.full numbers0 0 lv).
    cancel (IntArray.full out0 out_size0 nil).
  - split_pures.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial.
      unfold problem_9_spec.
      split.
      * rewrite rolling_max_f_Zlength. simpl in Hn. lia.
      * intros i Hi. lia.
Qed.

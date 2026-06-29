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
From SimpleC.EE.CAV.ground_truth_p136_largest_smallest_integers Require Import p136_largest_smallest_integers_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p136_largest_smallest_integers.
Local Open Scope sac.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Local Open Scope list_scope.

(* Proof helpers moved from p136_largest_smallest_integers.v so public contract files expose definitions only. *)

Lemma sublist_snoc_Znth_136 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ Znth i l 0 :: nil.
Proof.
  intros l i Hi.
  rewrite (sublist_split 0 (i + 1) i) by
    (try lia; rewrite <- Zlength_correct; lia).
  replace (sublist i (i + 1) l) with (Znth i l 0 :: nil).
  - reflexivity.
  - rewrite (sublist_single 0 i l) by lia.
    reflexivity.
Qed.
Lemma largest_negative_state_nil :
  largest_negative_state nil 0.
Proof.
  left.
  split; [reflexivity|].
  intros x H.
  contradiction.
Qed.
Lemma smallest_positive_state_nil :
  smallest_positive_state nil 0.
Proof.
  left.
  split; [reflexivity|].
  intros x H.
  contradiction.
Qed.
Lemma largest_smallest_prefix_init : forall l,
  0 <= Zlength l ->
  largest_smallest_prefix 0 l 0 0.
Proof.
  intros l Hlen.
  unfold largest_smallest_prefix.
  replace (sublist 0 0 l) with (@nil Z) by
    (symmetry; apply sublist_nil; lia).
  repeat split; try lia.
  - apply largest_negative_state_nil.
  - apply smallest_positive_state_nil.
Qed.
Lemma largest_negative_update_zero : forall s maxneg x,
  largest_negative_state s maxneg ->
  x < 0 ->
  maxneg = 0 ->
  largest_negative_state (s ++ x :: nil) x.
Proof.
  intros s maxneg x Hstate Hx Hmax.
  destruct Hstate as [[Hz Hnone] | [Hneg [Hin Hmaximal]]]; subst maxneg; try lia.
  right.
  repeat split; try lia.
  - apply in_or_app.
    right; simpl; auto.
  - intros y Hy Hyneg.
    apply in_app_or in Hy.
    destruct Hy as [Hy | [Hy | []]]; subst; try lia.
    specialize (Hnone y Hy).
    contradiction.
Qed.
Lemma largest_negative_update_bigger : forall s maxneg x,
  largest_negative_state s maxneg ->
  x < 0 ->
  maxneg <> 0 ->
  maxneg < x ->
  largest_negative_state (s ++ x :: nil) x.
Proof.
  intros s maxneg x Hstate Hx Hnonzero Hgt.
  destruct Hstate as [[Hz _] | [Hneg [Hin Hmaximal]]]; [contradiction|].
  right.
  repeat split; try lia.
  - apply in_or_app.
    right; simpl; auto.
  - intros y Hy Hyneg.
    apply in_app_or in Hy.
    destruct Hy as [Hy | [Hy | []]]; subst; try lia.
    specialize (Hmaximal y Hy Hyneg).
    lia.
Qed.
Lemma largest_negative_keep_nonneg : forall s maxneg x,
  largest_negative_state s maxneg ->
  x >= 0 ->
  largest_negative_state (s ++ x :: nil) maxneg.
Proof.
  intros s maxneg x Hstate Hx.
  destruct Hstate as [[Hz Hnone] | [Hneg [Hin Hmaximal]]].
  - left.
    split; [assumption|].
    intros y Hy Hyneg.
    apply in_app_or in Hy.
    destruct Hy as [Hy | [Hy | []]]; subst; try lia.
    apply (Hnone y Hy Hyneg).
  - right.
    repeat split; try assumption.
    + apply in_or_app; left; assumption.
    + intros y Hy Hyneg.
      apply in_app_or in Hy.
      destruct Hy as [Hy | [Hy | []]]; subst; try lia.
      apply Hmaximal; assumption.
Qed.
Lemma largest_negative_keep_not_bigger : forall s maxneg x,
  largest_negative_state s maxneg ->
  x < 0 ->
  maxneg <> 0 ->
  x <= maxneg ->
  largest_negative_state (s ++ x :: nil) maxneg.
Proof.
  intros s maxneg x Hstate Hx Hnonzero Hle.
  destruct Hstate as [[Hz _] | [Hneg [Hin Hmaximal]]]; [contradiction|].
  right.
  repeat split; try assumption.
  - apply in_or_app; left; assumption.
  - intros y Hy Hyneg.
    apply in_app_or in Hy.
    destruct Hy as [Hy | [Hy | []]]; subst; try lia.
    apply Hmaximal; assumption.
Qed.
Lemma smallest_positive_update_zero : forall s minpos x,
  smallest_positive_state s minpos ->
  x > 0 ->
  minpos = 0 ->
  smallest_positive_state (s ++ x :: nil) x.
Proof.
  intros s minpos x Hstate Hx Hmin.
  destruct Hstate as [[Hz Hnone] | [Hpos [Hin Hminimal]]]; subst minpos; try lia.
  right.
  repeat split; try lia.
  - apply in_or_app.
    right; simpl; auto.
  - intros y Hy Hypos.
    apply in_app_or in Hy.
    destruct Hy as [Hy | [Hy | []]]; subst; try lia.
    specialize (Hnone y Hy).
    contradiction.
Qed.
Lemma smallest_positive_update_smaller : forall s minpos x,
  smallest_positive_state s minpos ->
  x > 0 ->
  minpos <> 0 ->
  x < minpos ->
  smallest_positive_state (s ++ x :: nil) x.
Proof.
  intros s minpos x Hstate Hx Hnonzero Hlt.
  destruct Hstate as [[Hz _] | [Hpos [Hin Hminimal]]]; [contradiction|].
  right.
  repeat split; try lia.
  - apply in_or_app.
    right; simpl; auto.
  - intros y Hy Hypos.
    apply in_app_or in Hy.
    destruct Hy as [Hy | [Hy | []]]; subst; try lia.
    specialize (Hminimal y Hy Hypos).
    lia.
Qed.
Lemma smallest_positive_keep_nonpos : forall s minpos x,
  smallest_positive_state s minpos ->
  x <= 0 ->
  smallest_positive_state (s ++ x :: nil) minpos.
Proof.
  intros s minpos x Hstate Hx.
  destruct Hstate as [[Hz Hnone] | [Hpos [Hin Hminimal]]].
  - left.
    split; [assumption|].
    intros y Hy Hypos.
    apply in_app_or in Hy.
    destruct Hy as [Hy | [Hy | []]]; subst; try lia.
    apply (Hnone y Hy Hypos).
  - right.
    repeat split; try assumption.
    + apply in_or_app; left; assumption.
    + intros y Hy Hypos.
      apply in_app_or in Hy.
      destruct Hy as [Hy | [Hy | []]]; subst; try lia.
      apply Hminimal; assumption.
Qed.
Lemma smallest_positive_keep_not_smaller : forall s minpos x,
  smallest_positive_state s minpos ->
  x > 0 ->
  minpos <> 0 ->
  minpos <= x ->
  smallest_positive_state (s ++ x :: nil) minpos.
Proof.
  intros s minpos x Hstate Hx Hnonzero Hle.
  destruct Hstate as [[Hz _] | [Hpos [Hin Hminimal]]]; [contradiction|].
  right.
  repeat split; try assumption.
  - apply in_or_app; left; assumption.
  - intros y Hy Hypos.
    apply in_app_or in Hy.
    destruct Hy as [Hy | [Hy | []]]; subst; try lia.
    apply Hminimal; assumption.
Qed.
Lemma largest_smallest_prefix_step : forall i l maxneg minpos maxneg' minpos',
  0 <= i < Zlength l ->
  largest_smallest_prefix i l maxneg minpos ->
  largest_negative_state (sublist 0 (i + 1) l) maxneg' ->
  smallest_positive_state (sublist 0 (i + 1) l) minpos' ->
  largest_smallest_prefix (i + 1) l maxneg' minpos'.
Proof.
  intros i l maxneg minpos maxneg' minpos' Hi Hpre Hneg Hpos.
  unfold largest_smallest_prefix in *.
  repeat split; try lia; assumption.
Qed.
Lemma largest_smallest_prefix_min_zero : forall i l maxneg minpos,
  0 <= i < Zlength l ->
  largest_smallest_prefix i l maxneg minpos ->
  Znth i l 0 > 0 ->
  minpos = 0 ->
  largest_smallest_prefix (i + 1) l maxneg (Znth i l 0).
Proof.
  intros i l maxneg minpos Hi Hpre Hx Hmin.
  pose proof Hpre as Hpre_parts.
  destruct Hpre_parts as [Hbound [Hneg Hpos]].
  eapply largest_smallest_prefix_step with (maxneg := maxneg) (minpos := minpos); try eassumption.
    rewrite sublist_snoc_Znth_136 by lia.
    apply largest_negative_keep_nonneg; [assumption|lia].
  - rewrite sublist_snoc_Znth_136 by lia.
    apply smallest_positive_update_zero with (minpos := minpos); assumption.
Qed.
Lemma largest_smallest_prefix_min_smaller : forall i l maxneg minpos,
  0 <= i < Zlength l ->
  largest_smallest_prefix i l maxneg minpos ->
  Znth i l 0 > 0 ->
  minpos <> 0 ->
  Znth i l 0 < minpos ->
  largest_smallest_prefix (i + 1) l maxneg (Znth i l 0).
Proof.
  intros i l maxneg minpos Hi Hpre Hx Hnonzero Hlt.
  pose proof Hpre as Hpre_parts.
  destruct Hpre_parts as [Hbound [Hneg Hpos]].
  eapply largest_smallest_prefix_step with (maxneg := maxneg) (minpos := minpos); try eassumption.
    rewrite sublist_snoc_Znth_136 by lia.
    apply largest_negative_keep_nonneg; [assumption|lia].
  - rewrite sublist_snoc_Znth_136 by lia.
    apply smallest_positive_update_smaller with (minpos := minpos); assumption.
Qed.
Lemma largest_smallest_prefix_max_zero : forall i l maxneg minpos,
  0 <= i < Zlength l ->
  largest_smallest_prefix i l maxneg minpos ->
  Znth i l 0 < 0 ->
  maxneg = 0 ->
  largest_smallest_prefix (i + 1) l (Znth i l 0) minpos.
Proof.
  intros i l maxneg minpos Hi Hpre Hx Hmax.
  pose proof Hpre as Hpre_parts.
  destruct Hpre_parts as [Hbound [Hneg Hpos]].
  eapply largest_smallest_prefix_step with (maxneg := maxneg) (minpos := minpos); try eassumption.
  - rewrite sublist_snoc_Znth_136 by lia.
    apply largest_negative_update_zero with (maxneg := maxneg); assumption.
  - rewrite sublist_snoc_Znth_136 by lia.
    apply smallest_positive_keep_nonpos; [assumption|lia].
Qed.
Lemma largest_smallest_prefix_max_bigger : forall i l maxneg minpos,
  0 <= i < Zlength l ->
  largest_smallest_prefix i l maxneg minpos ->
  Znth i l 0 < 0 ->
  maxneg <> 0 ->
  maxneg < Znth i l 0 ->
  largest_smallest_prefix (i + 1) l (Znth i l 0) minpos.
Proof.
  intros i l maxneg minpos Hi Hpre Hx Hnonzero Hgt.
  pose proof Hpre as Hpre_parts.
  destruct Hpre_parts as [Hbound [Hneg Hpos]].
  eapply largest_smallest_prefix_step with (maxneg := maxneg) (minpos := minpos); try eassumption.
  - rewrite sublist_snoc_Znth_136 by lia.
    apply largest_negative_update_bigger with (maxneg := maxneg); assumption.
  - rewrite sublist_snoc_Znth_136 by lia.
    apply smallest_positive_keep_nonpos; [assumption|lia].
Qed.
Lemma largest_smallest_prefix_keep_zero : forall i l maxneg minpos,
  0 <= i < Zlength l ->
  largest_smallest_prefix i l maxneg minpos ->
  Znth i l 0 = 0 ->
  largest_smallest_prefix (i + 1) l maxneg minpos.
Proof.
  intros i l maxneg minpos Hi Hpre Hx.
  pose proof Hpre as Hpre_parts.
  destruct Hpre_parts as [Hbound [Hneg Hpos]].
  eapply largest_smallest_prefix_step with (maxneg := maxneg) (minpos := minpos); try eassumption.
  - rewrite sublist_snoc_Znth_136 by lia.
    apply largest_negative_keep_nonneg; [assumption|lia].
  - rewrite sublist_snoc_Znth_136 by lia.
    apply smallest_positive_keep_nonpos; [assumption|lia].
Qed.
Lemma largest_smallest_prefix_keep_negative : forall i l maxneg minpos,
  0 <= i < Zlength l ->
  largest_smallest_prefix i l maxneg minpos ->
  Znth i l 0 < 0 ->
  maxneg <> 0 ->
  Znth i l 0 <= maxneg ->
  largest_smallest_prefix (i + 1) l maxneg minpos.
Proof.
  intros i l maxneg minpos Hi Hpre Hx Hnonzero Hle.
  pose proof Hpre as Hpre_parts.
  destruct Hpre_parts as [Hbound [Hneg Hpos]].
  eapply largest_smallest_prefix_step with (maxneg := maxneg) (minpos := minpos); try eassumption.
  - rewrite sublist_snoc_Znth_136 by lia.
    apply largest_negative_keep_not_bigger; assumption.
  - rewrite sublist_snoc_Znth_136 by lia.
    apply smallest_positive_keep_nonpos; [assumption|lia].
Qed.
Lemma largest_smallest_prefix_keep_positive : forall i l maxneg minpos,
  0 <= i < Zlength l ->
  largest_smallest_prefix i l maxneg minpos ->
  Znth i l 0 > 0 ->
  minpos <> 0 ->
  minpos <= Znth i l 0 ->
  largest_smallest_prefix (i + 1) l maxneg minpos.
Proof.
  intros i l maxneg minpos Hi Hpre Hx Hnonzero Hle.
  pose proof Hpre as Hpre_parts.
  destruct Hpre_parts as [Hbound [Hneg Hpos]].
  eapply largest_smallest_prefix_step with (maxneg := maxneg) (minpos := minpos); try eassumption.
  - rewrite sublist_snoc_Znth_136 by lia.
    apply largest_negative_keep_nonneg; [assumption|lia].
  - rewrite sublist_snoc_Znth_136 by lia.
    apply smallest_positive_keep_not_smaller; assumption.
Qed.
Lemma largest_smallest_prefix_full_spec : forall l maxneg minpos,
  largest_smallest_prefix (Zlength l) l maxneg minpos ->
  let (a, b) := (neg_option_of_value maxneg, pos_option_of_value minpos) in
  is_largest_negative l a /\ is_smallest_positive l b.
Proof.
  intros l maxneg minpos Hpre.
  unfold largest_smallest_prefix in Hpre.
  destruct Hpre as [_ [Hneg Hpos]].
  rewrite sublist_self in Hneg by lia.
  rewrite sublist_self in Hpos by lia.
  split.
  - unfold neg_option_of_value.
    destruct (maxneg =? 0) eqn:Heq.
    + apply Z.eqb_eq in Heq.
      subst maxneg.
      destruct Hneg as [[_ Hnone] | [Hlt _]]; try lia.
      exact Hnone.
    + apply Z.eqb_neq in Heq.
      destruct Hneg as [[Hz _] | Hsome]; try contradiction.
      exact Hsome.
  - unfold pos_option_of_value.
    destruct (minpos =? 0) eqn:Heq.
    + apply Z.eqb_eq in Heq.
      subst minpos.
      destruct Hpos as [[_ Hnone] | [Hgt _]]; try lia.
      exact Hnone.
    + apply Z.eqb_neq in Heq.
      destruct Hpos as [[Hz _] | Hsome]; try contradiction.
      exact Hsome.
Qed.


Lemma proof_of_p136_largest_smallest_integers_entail_wit_1 : p136_largest_smallest_integers_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  apply largest_smallest_prefix_init.
  lia.
Qed.

Lemma proof_of_p136_largest_smallest_integers_entail_wit_2_1 : p136_largest_smallest_integers_entail_wit_2_1.
Proof.
  pre_process.
  entailer!.
  apply largest_smallest_prefix_min_zero with (minpos := minpos); try assumption; lia.
Qed.

Lemma proof_of_p136_largest_smallest_integers_entail_wit_2_2 : p136_largest_smallest_integers_entail_wit_2_2.
Proof.
  pre_process.
  entailer!.
  apply largest_smallest_prefix_min_smaller with (minpos := minpos); try assumption; lia.
Qed.

Lemma proof_of_p136_largest_smallest_integers_entail_wit_2_3 : p136_largest_smallest_integers_entail_wit_2_3.
Proof.
  pre_process.
  entailer!.
  apply largest_smallest_prefix_max_zero with (maxneg := maxneg); try assumption; lia.
Qed.

Lemma proof_of_p136_largest_smallest_integers_entail_wit_2_4 : p136_largest_smallest_integers_entail_wit_2_4.
Proof.
  pre_process.
  entailer!.
  apply largest_smallest_prefix_max_bigger with (maxneg := maxneg); try assumption; lia.
Qed.

Lemma proof_of_p136_largest_smallest_integers_entail_wit_2_5 : p136_largest_smallest_integers_entail_wit_2_5.
Proof.
  pre_process.
  entailer!.
  apply largest_smallest_prefix_keep_zero; try assumption; lia.
Qed.

Lemma proof_of_p136_largest_smallest_integers_entail_wit_2_6 : p136_largest_smallest_integers_entail_wit_2_6.
Proof.
  pre_process.
  entailer!.
  apply largest_smallest_prefix_keep_negative; try assumption; lia.
Qed.

Lemma proof_of_p136_largest_smallest_integers_entail_wit_2_7 : p136_largest_smallest_integers_entail_wit_2_7.
Proof.
  pre_process.
  entailer!.
  apply largest_smallest_prefix_keep_positive; try assumption; lia.
Qed.

Lemma proof_of_p136_largest_smallest_integers_return_wit_1 : p136_largest_smallest_integers_return_wit_1.
Proof.
  pre_process.
  replace i with lst_size_pre in * by lia.
  Exists (maxneg :: minpos :: nil) 2 retval_2.
  entailer!.
  - sep_apply (IntArray.seg_single retval_2 1 minpos).
    sep_apply (IntArray.seg_single retval_2 0 maxneg).
    sep_apply (IntArray.seg_merge_to_seg retval_2 0 1 2); [ | lia].
    sep_apply (IntArray.seg_to_full retval_2 0 2).
    replace (retval_2 + 0 * sizeof (INT)) with retval_2 by lia.
    replace (2 - 0) with 2 by lia.
    entailer!.
  - exists maxneg, minpos.
    split.
    + reflexivity.
    + split.
      * rewrite <- H4.
        assumption.
      * apply largest_smallest_prefix_full_spec.
        rewrite <- H4.
        assumption.
Qed.

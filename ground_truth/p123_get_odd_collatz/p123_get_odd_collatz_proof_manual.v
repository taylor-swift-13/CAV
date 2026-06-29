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
From SimpleC.EE.CAV.ground_truth_p123_get_odd_collatz Require Import p123_get_odd_collatz_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p123_get_odd_collatz.
Local Open Scope sac.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
From AUXLib Require Import ListLib.

Local Open Scope list_scope.

(* Proof helpers moved from p123_get_odd_collatz.v so public contract files expose definitions only. *)

Lemma problem_123_pre_initial : forall n,
  problem_123_pre n ->
  0 < n < INT_MAX /\ odd_collatz_prefix n n [1].
Proof.
  intros n Hpre.
  destruct Hpre as [Hn _].
  split; [assumption | constructor; lia].
Qed.
Lemma collatz_step_safe_of_pre : forall original current output,
  problem_123_pre original ->
  odd_collatz_prefix original current output ->
  0 < current < INT_MAX /\
  0 < 3 * current + 1 < INT_MAX /\
  (current <> 1 -> Zlength output < 1024) /\
  (current mod 2 = 0 ->
     0 < current / 2 < INT_MAX).
Proof.
  intros original current output Hpre Hprefix.
  destruct Hpre as [_ Hsafe].
  unfold collatz_step_safe in Hsafe.
  apply Hsafe; assumption.
Qed.
Lemma Z_rem_2_eq_1_to_mod : forall n,
  0 < n ->
  n % 2 = 1 ->
  n mod 2 = 1.
Proof.
  intros n Hn Hrem.
  rewrite Z.rem_mod_nonneg in Hrem by lia.
  exact Hrem.
Qed.
Lemma Z_rem_2_neq_1_to_mod_0 : forall n,
  0 < n ->
  n % 2 <> 1 ->
  n mod 2 = 0.
Proof.
  intros n Hn Hrem.
  assert (Hmod_bound : 0 <= n mod 2 < 2) by (apply Z.mod_pos_bound; lia).
  rewrite Z.rem_mod_nonneg in Hrem by lia.
  lia.
Qed.
Lemma odd_collatz_odd_quot_step : forall original n output,
  odd_collatz_prefix original n output ->
  n <> 1 ->
  0 < n ->
  n % 2 = 1 ->
  odd_collatz_prefix original (n * 3 + 1) (output ++ [n]).
Proof.
  intros original n output Hprefix Hnot1 Hpos Hodd.
  replace (n * 3 + 1) with (3 * n + 1) by lia.
  apply odd_collatz_odd; try assumption.
  apply Z_rem_2_eq_1_to_mod; assumption.
Qed.
Lemma odd_collatz_even_quot_step : forall original n output,
  odd_collatz_prefix original n output ->
  n <> 1 ->
  0 < n ->
  n % 2 <> 1 ->
  odd_collatz_prefix original (n ÷ 2) output.
Proof.
  intros original n output Hprefix Hnot1 Hpos Heven.
  replace (n ÷ 2) with (n / 2).
  - apply odd_collatz_even; try assumption.
    apply Z_rem_2_neq_1_to_mod_0; assumption.
  - symmetry. apply Z.quot_div_nonneg; lia.
Qed.
Lemma Zmod_1_even_false_123 : forall n,
  n mod 2 = 1 ->
  Z.even n = false.
Proof.
  intros n Hmod.
  rewrite Zmod_odd in Hmod.
  destruct (Z.odd n) eqn:Hodd.
  - rewrite <- Z.negb_odd.
    rewrite Hodd.
    reflexivity.
  - discriminate.
Qed.
Lemma Zmod_0_even_true_123 : forall n,
  n mod 2 = 0 ->
  Z.even n = true.
Proof.
  intros n Hmod.
  rewrite Zeven_mod.
  apply Zeq_is_eq_bool.
  exact Hmod.
Qed.
Lemma collatz_aux_app_path_123 : forall original current seq,
  collatz_list_to original current seq ->
  forall fuel,
    collatz_aux original (length seq + fuel)%nat =
    seq ++ collatz_aux current fuel.
Proof.
  intros original current seq Hpath.
  induction Hpath; intros fuel.
  - reflexivity.
  - rewrite app_length.
    simpl.
    replace (length seq + 1 + fuel)%nat with (length seq + S fuel)%nat by lia.
    rewrite IHHpath.
    simpl.
    destruct (n =? 1) eqn:Hn1.
    { apply Z.eqb_eq in Hn1. contradiction. }
    rewrite Zmod_1_even_false_123 by assumption.
    replace (n * 3 + 1) with (3 * n + 1) by lia.
    rewrite <- app_assoc.
    reflexivity.
  - rewrite app_length.
    simpl.
    replace (length seq + 1 + fuel)%nat with (length seq + S fuel)%nat by lia.
    rewrite IHHpath.
    simpl.
    destruct (n =? 1) eqn:Hn1.
    { apply Z.eqb_eq in Hn1. contradiction. }
    rewrite Zmod_0_even_true_123 by assumption.
    rewrite <- app_assoc.
    reflexivity.
Qed.
Lemma collatz_list_to_collatz_list_123 : forall original seq,
  collatz_list_to original 1 seq ->
  collatz_list original (seq ++ [1]).
Proof.
  intros original seq Hpath.
  unfold collatz_list.
  exists (length seq + 1)%nat.
  split.
  - rewrite collatz_aux_app_path_123 with (current := 1) (seq := seq) by assumption.
    simpl.
    reflexivity.
  - rewrite last_last.
    reflexivity.
Qed.
Lemma filter_odd_app_123 : forall l x,
  filter (fun x => Z.odd x) (l ++ [x]) =
  filter (fun x => Z.odd x) l ++
  if Z.odd x then [x] else [].
Proof.
  intros l x.
  rewrite filter_app.
  simpl.
  destruct (Z.odd x); reflexivity.
Qed.
Lemma odd_collatz_prefix_path_123 : forall original current raw_l,
  odd_collatz_prefix original current raw_l ->
  exists seq,
    collatz_list_to original current seq /\
    Permutation raw_l (1 :: filter (fun x => Z.odd x) seq).
Proof.
  intros original current raw_l Hprefix.
  induction Hprefix.
  - exists [].
    split.
    + constructor.
    + reflexivity.
  - destruct IHHprefix as [seq [Hpath Hperm]].
    exists (seq ++ [n]).
    split.
    + apply collatz_list_to_odd; assumption.
    + rewrite filter_odd_app_123.
      match goal with H : n mod 2 = 1 |- _ => rewrite Zmod_odd in H end.
      destruct (Z.odd n) eqn:Hodd.
      * simpl.
        eapply Permutation_trans.
        -- apply Permutation_app; [exact Hperm|reflexivity].
        -- reflexivity.
      * discriminate.
  - destruct IHHprefix as [seq [Hpath Hperm]].
    exists (seq ++ [n]).
    split.
    + apply collatz_list_to_even; assumption.
    + rewrite filter_odd_app_123.
      match goal with H : n mod 2 = 0 |- _ => rewrite Zmod_even in H end.
      destruct (Z.even n) eqn:Heven.
      * assert (Hodd : Z.odd n = false).
        {
          rewrite <- Z.negb_even.
          rewrite Heven.
          reflexivity.
        }
        rewrite Hodd.
        rewrite app_nil_r.
        exact Hperm.
      * discriminate.
Qed.
Lemma odd_collatz_prefix_original_spec_123 : forall original raw_l,
  odd_collatz_prefix original 1 raw_l ->
  exists c_seq,
    collatz_list original c_seq /\
    Permutation raw_l (filter (fun x => Z.odd x) c_seq).
Proof.
  intros original raw_l Hprefix.
  destruct (odd_collatz_prefix_path_123 _ _ _ Hprefix) as [seq [Hpath Hperm]].
  exists (seq ++ [1]).
  split.
  - apply collatz_list_to_collatz_list_123.
    exact Hpath.
  - rewrite filter_odd_app_123.
    simpl.
    eapply Permutation_trans.
    + exact Hperm.
    + rewrite <- (app_nil_r (1 :: filter (fun x : Z => Z.odd x) seq)).
      apply Permutation_middle.
Qed.
Lemma problem_123_spec_of_sorted : forall original raw_l sorted_l,
  odd_collatz_prefix original 1 raw_l ->
  sorted_int_list_by 1 sorted_l ->
  Permutation raw_l sorted_l ->
  problem_123_spec original sorted_l.
Proof.
  intros original raw_l sorted_l Hprefix Hsorted Hperm.
  unfold problem_123_spec.
  destruct (odd_collatz_prefix_original_spec_123 _ _ Hprefix)
    as [c_seq [Hcollatz Hraw_filter]].
  exists c_seq.
  repeat split.
  - exact Hcollatz.
  - eapply Permutation_trans.
    + apply Permutation_sym. exact Hperm.
    + exact Hraw_filter.
  - unfold sorted_int_list_by in Hsorted.
    simpl in Hsorted.
    exact Hsorted.
Qed.


Lemma proof_of_p123_get_odd_collatz_entail_wit_1 : p123_get_odd_collatz_entail_wit_1.
Proof.
  pre_process.
  Exists (cons 1 nil).
  sep_apply (IntArray.seg_single retval_2 0 1).
  entailer!.
  - apply problem_123_pre_initial in H1.
    tauto.
  - apply problem_123_pre_initial in H1.
    lia.
  - apply problem_123_pre_initial in H1.
    lia.
Qed.

Lemma proof_of_p123_get_odd_collatz_entail_wit_2 : p123_get_odd_collatz_entail_wit_2.
Proof.
  pre_process.
  Exists output_l_2.
  pose proof (collatz_step_safe_of_pre n_pre n output_l_2 H2 H8) as [_ [Hnext [Hroom _]]].
  entailer!.
  all: try lia.
Qed.

Lemma proof_of_p123_get_odd_collatz_entail_wit_4 : p123_get_odd_collatz_entail_wit_4.
Proof.
  pre_process.
  Exists (output_l_2 ++ n :: nil).
  pose proof (collatz_step_safe_of_pre n_pre n output_l_2 H3 H12) as [_ [Hnext _]].
  entailer!.
  - apply odd_collatz_odd_quot_step; try assumption; lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
Qed.

Lemma proof_of_p123_get_odd_collatz_entail_wit_5_1 : p123_get_odd_collatz_entail_wit_5_1.
Proof.
  pre_process.
  Exists output_l_2.
  pose proof (collatz_step_safe_of_pre n_pre n output_l_2 H3 H15) as [_ [_ [_ Heven_bounds]]].
  assert (Hmod : n mod 2 = 0) by (apply Z_rem_2_neq_1_to_mod_0; lia).
  assert (Hdiv : n ÷ 2 = n / 2) by (apply Z.quot_div_nonneg; lia).
  entailer!.
  - apply odd_collatz_even_quot_step; assumption.
Qed.

Lemma proof_of_p123_get_odd_collatz_entail_wit_6 : p123_get_odd_collatz_entail_wit_6.
Proof.
  pre_process.
  subst n.
  Exists output_l_2.
  entailer!.
Qed.

Lemma proof_of_p123_get_odd_collatz_entail_wit_7 : p123_get_odd_collatz_entail_wit_7.
Proof.
  pre_process.
  Exists sorted_full_l sorted_l_2 output_l_2.
  entailer!.
  apply problem_123_spec_of_sorted with (raw_l := output_l_2); assumption.
Qed.

Lemma proof_of_p123_get_odd_collatz_return_wit_1 : p123_get_odd_collatz_return_wit_1.
Proof.
  pre_process.
  Exists data_l_2 sorted_l output_size_2 data_2.
  entailer!.
Qed.

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
From SimpleC.EE.CAV.ground_truth_p068_pluck Require Import p068_pluck_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p068_pluck.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p068_pluck.v so public contract files expose definitions only. *)

Lemma pluck_scan_from_app : forall l1 l2 i best,
  pluck_scan_from i (l1 ++ l2) best =
  pluck_scan_from (i + Zlength l1) l2 (pluck_scan_from i l1 best).
Proof.
  induction l1 as [|x xs IH]; intros l2 i best; simpl.
  - change (Zlength (@nil Z)) with 0.
    replace (i + 0) with i by lia.
    reflexivity.
  - rewrite IH.
    rewrite Zlength_cons.
    replace (i + Z.succ (Zlength xs)) with (i + 1 + Zlength xs) by lia.
    reflexivity.
Qed.
Lemma pluck_prefix_result_0 : forall arr,
  pluck_loop_state arr 0 [].
Proof.
  intros arr.
  unfold pluck_loop_state, pluck_prefix_result.
  rewrite Zsublist_nil by lia.
  simpl.
  rewrite Zlength_correct.
  split; [lia | reflexivity].
Qed.
Lemma pluck_prefix_result_step : forall arr i,
  0 <= i < Zlength arr ->
  pluck_prefix_result arr (i + 1) =
  pluck_update (Znth i arr 0) i (pluck_prefix_result arr i).
Proof.
  intros arr i Hi.
  destruct Hi as [Hi0 Hilt].
  rewrite Zlength_correct in Hilt.
  unfold pluck_prefix_result.
  assert (Hsplit: sublist 0 (i + 1) arr = sublist 0 i arr ++ sublist i (i + 1) arr).
  { rewrite (sublist_split 0 (i + 1) i arr) by (rewrite ?Zlength_correct; lia).
    reflexivity. }
  rewrite Hsplit.
  rewrite pluck_scan_from_app.
  rewrite Zlength_sublist by (rewrite Zlength_correct; split; lia).
  rewrite (sublist_single 0 i arr) by (rewrite ?Zlength_correct; lia).
  simpl.
  replace (0 + i) with i by lia.
  replace (i - 0) with i by lia.
  reflexivity.
Qed.
Lemma replace_Znth_two : forall a b l,
  Zlength l = 2 ->
  @replace_Znth Z 1 b (@replace_Znth Z 0 a l) = [a; b].
Proof.
  intros a b l Hlen.
  rewrite Zlength_correct in Hlen.
  destruct l as [|x [|y [|z zs]]]; simpl in Hlen; try lia.
  reflexivity.
Qed.
Lemma pluck_loop_state_update_empty : forall arr i output,
  0 <= i < Zlength arr ->
  pluck_loop_state arr i output ->
  output = [] ->
  Z.rem (Znth i arr 0) 2 = 0 ->
  pluck_loop_state arr (i + 1) [Znth i arr 0; i].
Proof.
  intros arr i output Hi [Hrange Hstate] Hout Heven.
  unfold pluck_loop_state.
  split; [lia |].
  rewrite pluck_prefix_result_step by lia.
  rewrite <- Hstate.
  unfold pluck_update.
  apply Z.eqb_eq in Heven.
  rewrite Heven.
  rewrite Hout.
  reflexivity.
Qed.
Lemma pluck_loop_state_update_less : forall arr i output value index,
  0 <= i < Zlength arr ->
  pluck_loop_state arr i output ->
  output = [value; index] ->
  Z.rem (Znth i arr 0) 2 = 0 ->
  Znth i arr 0 < Znth 0 output 0 ->
  pluck_loop_state arr (i + 1) [Znth i arr 0; i].
Proof.
  intros arr i output value index Hi [Hrange Hstate] Hout Heven Hlt.
  unfold pluck_loop_state.
  split; [lia |].
  rewrite pluck_prefix_result_step by lia.
  rewrite <- Hstate.
  unfold pluck_update.
  apply Z.eqb_eq in Heven.
  rewrite Heven.
  rewrite Hout.
  rewrite Hout in Hlt.
  change (Znth 0 [value; index] 0) with value in Hlt.
  simpl in Hlt.
  apply Z.ltb_lt in Hlt.
  rewrite Hlt.
  reflexivity.
Qed.
Lemma pluck_loop_state_skip_odd : forall arr i output,
  0 <= i < Zlength arr ->
  pluck_loop_state arr i output ->
  Z.rem (Znth i arr 0) 2 <> 0 ->
  pluck_loop_state arr (i + 1) output.
Proof.
  intros arr i output Hi [Hrange Hstate] Hodd.
  unfold pluck_loop_state.
  split; [lia |].
  rewrite pluck_prefix_result_step by lia.
  rewrite <- Hstate.
  unfold pluck_update.
  apply Z.eqb_neq in Hodd.
  rewrite Hodd.
  reflexivity.
Qed.
Lemma pluck_loop_state_skip_ge : forall arr i output value index,
  0 <= i < Zlength arr ->
  pluck_loop_state arr i output ->
  output = [value; index] ->
  Z.rem (Znth i arr 0) 2 = 0 ->
  Znth i arr 0 >= Znth 0 output 0 ->
  pluck_loop_state arr (i + 1) output.
Proof.
  intros arr i output value index Hi [Hrange Hstate] Hout Heven Hge.
  unfold pluck_loop_state.
  split; [lia |].
  rewrite pluck_prefix_result_step by lia.
  rewrite <- Hstate.
  unfold pluck_update.
  apply Z.eqb_eq in Heven.
  rewrite Heven.
  rewrite Hout.
  rewrite Hout in Hge.
  change (Znth 0 [value; index] 0) with value in Hge.
  simpl in Hge.
  assert (Hge' : value <= Znth i arr 0) by lia.
  apply Z.ltb_ge in Hge'.
  rewrite Hge'.
  reflexivity.
Qed.
Lemma pluck_best_spec_update : forall base processed best x,
  pluck_best_spec base processed best ->
  pluck_best_spec base (processed ++ [x])
    (pluck_update x (base + Zlength processed) best).
Proof.
  intros base processed best x Hbest.
  unfold pluck_update.
  destruct (Z.eqb (Z.rem x 2) 0) eqn:Heven.
  - apply Z.eqb_eq in Heven.
    destruct best as [|value [|index [|extra rest]]]; simpl in Hbest; try contradiction.
    + simpl.
      exists (length processed).
      repeat split.
      * rewrite Zlength_correct. lia.
      * rewrite nth_error_app2 by lia.
        replace (length processed - length processed)%nat with 0%nat by lia.
        reflexivity.
      * exact Heven.
      * intros y Hy Hy_even.
        apply in_app_or in Hy.
        destruct Hy as [Hy | [Hy | []]].
        -- exfalso. apply (Hbest y Hy Hy_even).
        -- subst y. lia.
      * intros j Hj.
        rewrite app_nth1 by lia.
        intro Hnth.
        apply Hbest with (x := nth j processed 0).
        -- apply nth_In. lia.
        -- rewrite Hnth. exact Heven.
    + destruct (Z.ltb x value) eqn:Hlt.
      * apply Z.ltb_lt in Hlt.
        destruct Hbest as [idx [Hindex [Hnth [Hvalue_even [Hmin Hfirst]]]]].
        simpl.
        exists (length processed).
        repeat split.
        -- rewrite Zlength_correct. lia.
        -- rewrite nth_error_app2 by lia.
           replace (length processed - length processed)%nat with 0%nat by lia.
           reflexivity.
        -- exact Heven.
        -- intros y Hy Hy_even.
           apply in_app_or in Hy.
           destruct Hy as [Hy | [Hy | []]].
           ++ specialize (Hmin y Hy Hy_even). lia.
           ++ subst y. lia.
        -- intros j Hj.
           rewrite app_nth1 by lia.
           intro Hnth_j.
           destruct (Z.eq_dec (Z.rem (nth j processed 0) 2) 0) as [Hj_even | Hj_odd].
           ++ assert (Hin_j : In (nth j processed 0) processed).
              { apply nth_In. exact Hj. }
              specialize (Hmin (nth j processed 0) Hin_j Hj_even).
              lia.
           ++ rewrite Hnth_j in Hj_odd. contradiction.
      * apply Z.ltb_ge in Hlt.
        destruct Hbest as [idx [Hindex [Hnth [Hvalue_even [Hmin Hfirst]]]]].
        simpl.
        exists idx.
        repeat split.
        -- exact Hindex.
        -- rewrite nth_error_app1; [exact Hnth |].
           apply nth_error_Some.
           rewrite Hnth. discriminate.
        -- exact Hvalue_even.
        -- intros y Hy Hy_even.
           apply in_app_or in Hy.
           destruct Hy as [Hy | [Hy | []]].
           ++ apply Hmin; auto.
           ++ subst y. lia.
        -- intros j Hj.
           rewrite app_nth1.
           ++ apply Hfirst. exact Hj.
           ++ apply nth_error_Some.
              destruct (nth_error processed j) eqn:Hnth_j; [discriminate |].
              assert (Hj_len : (length processed <= j)%nat).
              { apply nth_error_None. exact Hnth_j. }
              assert (Hidx_len : (idx < length processed)%nat).
              { apply nth_error_Some. rewrite Hnth. discriminate. }
              lia.
  - apply Z.eqb_neq in Heven.
    destruct best as [|value [|index [|extra rest]]]; simpl in Hbest; try contradiction.
    + simpl.
      intros y Hy.
      apply in_app_or in Hy.
      destruct Hy as [Hy | [Hy | []]]; subst; auto.
    + destruct Hbest as [idx [Hindex [Hnth [Hvalue_even [Hmin Hfirst]]]]].
      simpl.
      exists idx.
      repeat split.
      * exact Hindex.
      * rewrite nth_error_app1; [exact Hnth |].
        apply nth_error_Some.
        rewrite Hnth. discriminate.
      * exact Hvalue_even.
      * intros y Hy Hy_even.
        apply in_app_or in Hy.
        destruct Hy as [Hy | [Hy | []]].
        -- apply Hmin; auto.
        -- subst y. contradiction.
      * intros j Hj.
        rewrite app_nth1.
        -- apply Hfirst. exact Hj.
        -- apply nth_error_Some.
           destruct (nth_error processed j) eqn:Hnth_j; [discriminate |].
           assert (Hj_len : (length processed <= j)%nat).
           { apply nth_error_None. exact Hnth_j. }
           assert (Hidx_len : (idx < length processed)%nat).
           { apply nth_error_Some. rewrite Hnth. discriminate. }
           lia.
Qed.
Lemma pluck_scan_from_best_spec : forall rest base processed best,
  pluck_best_spec base processed best ->
  pluck_best_spec base (processed ++ rest)
    (pluck_scan_from (base + Zlength processed) rest best).
Proof.
  induction rest as [|x xs IH]; intros base processed best Hbest; simpl.
  - rewrite app_nil_r. exact Hbest.
  - replace (base + Zlength processed + 1)
      with (base + Zlength (processed ++ [x])) by
        (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    replace (processed ++ x :: xs) with ((processed ++ [x]) ++ xs)
      by (rewrite <- app_assoc; reflexivity).
    apply IH.
    apply pluck_best_spec_update.
    exact Hbest.
Qed.
Lemma pluck_prefix_result_best_spec : forall arr,
  pluck_best_spec 0 arr (pluck_prefix_result arr (Zlength arr)).
Proof.
  intros arr.
  unfold pluck_prefix_result.
  rewrite (sublist_self arr (Zlength arr)) by lia.
  replace 0 with (0 + Zlength (@nil Z)) by reflexivity.
  change arr with (@nil Z ++ arr) at 1.
  apply pluck_scan_from_best_spec.
  simpl.
  intros x H; contradiction.
Qed.
Lemma pluck_loop_state_full_spec : forall arr i output,
  list_nonnegative arr ->
  i >= Zlength arr ->
  pluck_loop_state arr i output ->
  problem_68_spec arr output.
Proof.
  intros arr i output Hnonneg Hi [Hrange Hstate].
  unfold problem_68_spec.
  split; [exact Hnonneg |].
  replace i with (Zlength arr) in Hstate by lia.
  rewrite Hstate.
  apply pluck_prefix_result_best_spec.
Qed.


Lemma proof_of_p068_pluck_entail_wit_1 : p068_pluck_entail_wit_1.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros2.
  Exists (@nil Z) 0.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply pluck_prefix_result_0.
Qed.

Lemma proof_of_p068_pluck_entail_wit_2_1 : p068_pluck_entail_wit_2_1.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros2.
  Exists (Znth i input_l 0) i (cons (Znth i input_l 0) (cons i nil)) 2.
  sep_apply (IntArray.seg_single data 1 i).
  sep_apply (IntArray.seg_single data 0 (Znth i input_l 0)).
  sep_apply (IntArray.seg_merge_to_full data 0 1 2
               (Znth i input_l 0 :: nil) (i :: nil)); [ | lia].
  replace (data + 0 * sizeof (INT)) with data by lia.
  replace (2 - 0) with 2 by lia.
  simpl.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply pluck_loop_state_update_empty with (output := output_l_2); auto; lia.
Qed.

Lemma proof_of_p068_pluck_entail_wit_2_2 : p068_pluck_entail_wit_2_2.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros2.
  Exists (Znth i input_l 0) i
         (replace_Znth 1 i (replace_Znth 0 (Znth i input_l 0) output_l_2)) 2.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  - rewrite replace_Znth_two by lia. reflexivity.
  - rewrite replace_Znth_two by lia.
    apply pluck_loop_state_update_less with
      (output := output_l_2) (value := value_2) (index := index_2);
      auto; lia.
  - rewrite replace_Znth_two by lia. reflexivity.
Qed.

Lemma proof_of_p068_pluck_entail_wit_2_3 : p068_pluck_entail_wit_2_3.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros2.
  Exists output_l_2 0.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply pluck_loop_state_skip_odd; auto; lia.
Qed.

Lemma proof_of_p068_pluck_entail_wit_2_4 : p068_pluck_entail_wit_2_4.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros2.
  Exists value_2 index_2 output_l_2 2.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply pluck_loop_state_skip_odd; auto; lia.
Qed.

Lemma proof_of_p068_pluck_entail_wit_2_5 : p068_pluck_entail_wit_2_5.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros2.
  Exists value_2 index_2 output_l_2 2.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply pluck_loop_state_skip_ge with
    (value := value_2) (index := index_2); auto; lia.
Qed.

Lemma proof_of_p068_pluck_return_wit_1 : p068_pluck_return_wit_1.
Proof.
  pre_process.
  subst output_l_2 output_size_2.
  rewrite <- derivable1_orp_intros1.
  Exists data_2 (@nil Z) 0.
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply pluck_loop_state_full_spec with (i := i); auto; lia.
Qed.

Lemma proof_of_p068_pluck_return_wit_2 : p068_pluck_return_wit_2.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  Exists data_2 output_l_2 2.
  sep_apply (IntArray.full_to_seg data_2 2 output_l_2).
  rewrite (IntArray.undef_seg_empty data_2 2).
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply pluck_loop_state_full_spec with (i := i); auto; lia.
Qed.

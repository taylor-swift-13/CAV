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
From SimpleC.EE.CAV.ground_truth_p034_unique Require Import p034_unique_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p034_unique.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p034_unique.v so public contract files expose definitions only. *)

Lemma Znth_In_range : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma In_Znth_exists : forall (x : Z) l,
  In x l ->
  exists i, 0 <= i < Zlength l /\ Znth i l 0 = x.
Proof.
  intros x l Hin.
  apply In_nth_error in Hin.
  destruct Hin as [n Hn].
  exists (Z.of_nat n).
  split.
  - assert ((n < length l)%nat) as Hlt.
    { apply nth_error_Some. rewrite Hn. discriminate. }
    rewrite Zlength_correct.
    lia.
  - unfold Znth.
    rewrite Nat2Z.id.
    apply nth_error_nth with (d := 0) in Hn.
    exact Hn.
Qed.
Lemma sublist_snoc_Znth : forall (l : list Z) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0].
Proof.
  intros l i Hi.
  pose proof (@sublist_split Z 0 (i + 1) i l
    ltac:(destruct Hi; lia) ltac:(destruct Hi; lia)) as Hsplit.
  rewrite Hsplit.
  rewrite (@sublist_single Z 0 i l) by (destruct Hi; lia).
  reflexivity.
Qed.
Lemma seen_values_aux_app_one : forall xs seen x,
  seen_values_aux seen (xs ++ [x]) =
  let seen' := seen_values_aux seen xs in
  if in_dec Z.eq_dec x seen' then seen' else seen' ++ [x].
Proof.
  induction xs as [| y ys IH]; intros seen x; simpl.
  - reflexivity.
  - destruct (in_dec Z.eq_dec y seen); apply IH.
Qed.
Lemma seen_values_snoc_seen : forall xs x,
  In x (seen_values xs) ->
  seen_values (xs ++ [x]) = seen_values xs.
Proof.
  intros xs x Hin.
  unfold seen_values in *.
  rewrite seen_values_aux_app_one.
  change ((if in_dec Z.eq_dec x (seen_values_aux [] xs)
           then seen_values_aux [] xs
           else seen_values_aux [] xs ++ [x]) = seen_values_aux [] xs).
  destruct (in_dec Z.eq_dec x (seen_values_aux [] xs)); [reflexivity | contradiction].
Qed.
Lemma seen_values_snoc_new : forall xs x,
  ~ In x (seen_values xs) ->
  seen_values (xs ++ [x]) = seen_values xs ++ [x].
Proof.
  intros xs x Hnot.
  unfold seen_values in *.
  rewrite seen_values_aux_app_one.
  change ((if in_dec Z.eq_dec x (seen_values_aux [] xs)
           then seen_values_aux [] xs
           else seen_values_aux [] xs ++ [x]) = seen_values_aux [] xs ++ [x]).
  destruct (in_dec Z.eq_dec x (seen_values_aux [] xs)); [contradiction | reflexivity].
Qed.
Lemma unique_first_loop_add : forall input i output x,
  x = Znth i input 0 ->
  0 <= i < Zlength input ->
  list_not_contains x output ->
  unique_first_loop input i output ->
  unique_first_loop input (i + 1) (output ++ [x]).
Proof.
  intros input i output x Hx Hi Hnot Hloop.
  unfold unique_first_loop in *.
  destruct Hloop as [Hrange Hout].
  split; [lia |].
  rewrite sublist_snoc_Znth by lia.
  rewrite <- Hx.
  rewrite seen_values_snoc_new.
  - rewrite <- Hout. reflexivity.
  - unfold list_not_contains in Hnot. rewrite <- Hout. exact Hnot.
Qed.
Lemma unique_first_loop_skip : forall input i output x,
  x = Znth i input 0 ->
  0 <= i < Zlength input ->
  list_contains x output ->
  unique_first_loop input i output ->
  unique_first_loop input (i + 1) output.
Proof.
  intros input i output x Hx Hi Hin Hloop.
  unfold unique_first_loop in *.
  destruct Hloop as [Hrange Hout].
  split; [lia |].
  rewrite sublist_snoc_Znth by lia.
  rewrite <- Hx.
  rewrite seen_values_snoc_seen.
  - exact Hout.
  - unfold list_contains in Hin. rewrite <- Hout. exact Hin.
Qed.
Lemma seen_values_aux_In_iff : forall rest seen x,
  In x (seen_values_aux seen rest) <-> In x seen \/ In x rest.
Proof.
  induction rest as [| y ys IH]; intros seen x; simpl.
  - tauto.
  - destruct (in_dec Z.eq_dec y seen) as [Hy | Hy].
    + rewrite IH. split; intros H.
      * destruct H as [H | H]; auto.
      * destruct H as [H | [H | H]]; subst; auto.
    + rewrite IH. split; intros H.
      * destruct H as [H | H].
        -- apply in_app_or in H. destruct H as [H | [H | []]]; subst; auto.
        -- auto.
      * destruct H as [H | [H | H]]; subst; auto.
        -- left. apply in_or_app. left. exact H.
        -- left. apply in_or_app. right. simpl; auto.
Qed.
Lemma seen_values_In_iff : forall input x,
  In x (seen_values input) <-> In x input.
Proof.
  intros input x.
  unfold seen_values.
  rewrite seen_values_aux_In_iff.
  split.
  - intros [H | H]; [contradiction | exact H].
  - intros H. right. exact H.
Qed.
Lemma seen_values_aux_NoDup_simple : forall rest seen,
  NoDup seen ->
  NoDup (seen_values_aux seen rest).
Proof.
  induction rest as [| y ys IH]; intros seen Hnodup; simpl.
  - exact Hnodup.
  - destruct (in_dec Z.eq_dec y seen) as [Hy | Hy].
    + apply IH. exact Hnodup.
    + apply IH.
      apply NoDup_app.
      repeat split.
      * exact Hnodup.
      * constructor; [intro H; inversion H | constructor].
      * intros z Hz Hz_tail.
        destruct Hz_tail as [Hz_eq | []].
        subst z. contradiction.
Qed.
Lemma seen_values_NoDup : forall input,
  NoDup (seen_values input).
Proof.
  intros input.
  unfold seen_values.
  apply seen_values_aux_NoDup_simple.
  constructor.
Qed.
Lemma unique_first_loop_full : forall input output,
  unique_first_loop input (Zlength input) output ->
  output = seen_values input.
Proof.
  intros input output Hloop.
  unfold unique_first_loop in Hloop.
  destruct Hloop as [_ Hout].
  rewrite (sublist_self input (Zlength input) eq_refl) in Hout.
  exact Hout.
Qed.
Lemma problem_34_spec_from_sort : forall input unique_l output,
  unique_first_loop input (Zlength input) unique_l ->
  sorted_int_list_by 1 output ->
  Permutation unique_l output ->
  problem_34_spec input output.
Proof.
  intros input unique_l output Hloop Hsorted Hperm.
  unfold problem_34_spec, problem_34_spec.
  split.
  - simpl in Hsorted. exact Hsorted.
  - split.
    + apply (Permutation_NoDup Hperm).
      rewrite (unique_first_loop_full input unique_l Hloop).
      apply seen_values_NoDup.
    + intros z.
      split; intros Hin.
      * eapply Permutation_in.
        -- exact Hperm.
        -- 
        rewrite (unique_first_loop_full input unique_l Hloop).
        rewrite seen_values_In_iff.
        exact Hin.
      * rewrite <- seen_values_In_iff.
        rewrite <- (unique_first_loop_full input unique_l Hloop).
        eapply Permutation_in.
        -- apply Permutation_sym. exact Hperm.
        --
        exact Hin.
Qed.


Lemma proof_of_contains_entail_wit_2 : contains_entail_wit_2.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  intros k Hk.
  destruct (Z.eq_dec k i).
  - subst. replace (i - 0) with i in H by lia. exact H.
  - apply H4. lia.
Qed.

Lemma proof_of_contains_return_wit_1 : contains_return_wit_1.
Proof.
  pre_process.
  Right.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  unfold list_not_contains.
  intros Hin.
  destruct (In_Znth_exists _ _ Hin) as [j [? Hj]].
  specialize (H3 j ltac:(lia)).
  congruence.
Qed.

Lemma proof_of_contains_return_wit_2 : contains_return_wit_2.
Proof.
  pre_process.
  Left.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  unfold list_contains.
  rewrite <- H.
  replace (i - 0) with i by lia.
  apply Znth_In_range.
  lia.
Qed.

Lemma proof_of_p034_unique_entail_wit_1 : p034_unique_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z).
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  unfold unique_first_loop, seen_values.
  simpl.
  repeat split; lia.
Qed.

Lemma proof_of_p034_unique_entail_wit_2_1 : p034_unique_entail_wit_2_1.
Proof.
  pre_process.
  Exists (output_l_2 ++ (Znth i input_l 0 :: nil)).
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  - apply unique_first_loop_add with (x := Znth i input_l 0); try reflexivity; try assumption; lia.
  - rewrite Zlength_app. change (Zlength (Znth i input_l 0 :: nil)) with 1. lia.
Qed.

Lemma proof_of_p034_unique_entail_wit_2_2 : p034_unique_entail_wit_2_2.
Proof.
  pre_process.
  Exists output_l_2.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply unique_first_loop_skip with (x := Znth i input_l 0); try reflexivity; try assumption; lia.
Qed.

Lemma proof_of_p034_unique_return_wit_1 : p034_unique_return_wit_1.
Proof.
  pre_process.
  Exists sorted_full_l sorted_l output_size_2 data_2.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply problem_34_spec_from_sort with (unique_l := output_l_2); try assumption.
  replace (Zlength input_l) with i by lia.
  assumption.
Qed.

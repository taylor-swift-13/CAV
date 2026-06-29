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
From SimpleC.EE.CAV.ground_truth_p120_maximum Require Import p120_maximum_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p120_maximum.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p120_maximum.v so public contract files expose definitions only. *)

Lemma problem_120_pre_k_bounds : forall input k,
  problem_120_pre input k ->
  0 <= k <= Zlength input.
Proof.
  intros input k Hpre.
  unfold problem_120_pre in Hpre.
  tauto.
Qed.
Lemma problem_120_pre_Znth_range : forall input k i,
  problem_120_pre input k ->
  0 <= i < Zlength input ->
  -1000 <= Znth i input 0 <= 1000.
Proof.
  intros input k i Hpre Hi.
  unfold problem_120_pre in Hpre.
  destruct Hpre as [_ [Hforall _]].
  rewrite Forall_forall in Hforall.
  apply Hforall.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma copy_prefix_nil : forall input,
  copy_prefix input 0 = [].
Proof.
  intros.
  unfold copy_prefix.
  apply sublist_nil.
  lia.
Qed.
Lemma copy_prefix_snoc : forall input i,
  0 <= i < Zlength input ->
  copy_prefix input (i + 1) = copy_prefix input i ++ [Znth i input 0].
Proof.
  intros input i Hi.
  unfold copy_prefix.
  rewrite (sublist_split 0 (i + 1) i input).
  replace (sublist i (i + 1) input) with (Znth i input 0 :: nil).
  replace (i + 1 - 0) with (i + 1) by lia.
  replace (i - 0) with i by lia.
  reflexivity.
  - symmetry. apply sublist_single.
    lia.
  - lia.
  - lia.
Qed.
Lemma copy_prefix_full : forall input size,
  size = Zlength input ->
  copy_prefix input size = input.
Proof.
  intros input size Hsize.
  unfold copy_prefix.
  apply sublist_self.
  lia.
Qed.
Lemma maximum_output_prefix_nil : forall sorted_l size k,
  maximum_output_prefix sorted_l size k 0 = [].
Proof.
  intros.
  unfold maximum_output_prefix.
  apply sublist_nil.
  lia.
Qed.
Lemma maximum_output_prefix_snoc : forall sorted_l size k i,
  size = Zlength sorted_l ->
  0 < k <= size ->
  0 <= i < k ->
  maximum_output_prefix sorted_l size k (i + 1) =
    maximum_output_prefix sorted_l size k i ++ [Znth (size - k + i) sorted_l 0].
Proof.
  intros sorted_l size k i Hsize Hk Hi.
  unfold maximum_output_prefix.
  rewrite (sublist_split (size - k) (size - k + (i + 1)) (size - k + i) sorted_l).
  replace (size - k + (i + 1)) with (size - k + i + 1) by lia.
  replace (sublist (size - k + i) (size - k + i + 1) sorted_l)
    with (Znth (size - k + i) sorted_l 0 :: nil).
  reflexivity.
  - symmetry. apply sublist_single.
    lia.
  - lia.
  - lia.
Qed.
Lemma maximum_output_prefix_Zlength : forall sorted_l size k i,
  size = Zlength sorted_l ->
  0 <= i <= k ->
  0 <= k <= size ->
  Zlength (maximum_output_prefix sorted_l size k i) = i.
Proof.
  intros sorted_l size k i Hsize Hi Hk.
  unfold maximum_output_prefix.
  rewrite Zlength_sublist by lia.
  lia.
Qed.
Lemma problem_120_spec_nil : forall input,
  problem_120_spec input 0 [].
Proof.
  intros.
  unfold problem_120_spec.
  split.
  - reflexivity.
  - split.
    + constructor.
    + exists input.
      split.
      * reflexivity.
      * intros x y Hx _.
        contradiction.
Qed.
Lemma IntArray_undef_full_0_to_full_nil : forall p,
  IntArray.undef_full p 0 |-- IntArray.full p 0 (@nil Z).
Proof.
  intros.
  rewrite IntArray.undef_full_empty.
  unfold IntArray.full, store_array, store_array_rec.
  entailer!.
Qed.
Lemma Sorted_cons_all_le_120 : forall x l y,
  Sorted Z.le (x :: l) ->
  In y (x :: l) ->
  x <= y.
Proof.
  intros x l.
  revert x.
  induction l; intros x y Hsorted Hin.
  - simpl in Hin.
    destruct Hin as [-> | []].
    lia.
  - simpl in Hin.
    destruct Hin as [-> | Hin].
    + lia.
    + pose proof (Sorted_inv Hsorted) as [Htail Hhd].
      assert (x <= a).
      {
        inversion Hhd; subst.
        assumption.
      }
      assert (a <= y).
      {
        apply IHl.
        - exact Htail.
        - simpl. exact Hin.
      }
      lia.
Qed.
Lemma nth_sorted_le_nat_120 : forall l n m d,
  Sorted Z.le l ->
  (n <= m < length l)%nat ->
  nth n l d <= nth m l d.
Proof.
  induction l; intros n m d Hsorted Hrange.
  - simpl in Hrange. lia.
  - destruct n; destruct m; simpl.
    + lia.
    + apply (Sorted_cons_all_le_120 a l (nth m l d)).
      * exact Hsorted.
      * right. apply nth_In. simpl in Hrange. lia.
    + lia.
    + pose proof (Sorted_inv Hsorted) as [Htail _].
      apply IHl.
      * exact Htail.
      * simpl in Hrange. lia.
Qed.
Lemma Sorted_app_right_120 : forall l1 l2,
  Sorted Z.le (l1 ++ l2) ->
  Sorted Z.le l2.
Proof.
  induction l1; intros l2 Hsorted.
  - simpl in Hsorted. exact Hsorted.
  - apply IHl1.
    pose proof (Sorted_inv Hsorted) as [Htail _].
    exact Htail.
Qed.
Lemma Sorted_app_all_le_120 : forall l1 l2 x y,
  Sorted Z.le (l1 ++ l2) ->
  In y l1 ->
  In x l2 ->
  y <= x.
Proof.
  intros l1 l2 x y Hsorted Hy Hx.
  destruct (In_nth l1 y 0 Hy) as [i [Hi Hy_nth]].
  destruct (In_nth l2 x 0 Hx) as [j [Hj Hx_nth]].
  subst y x.
  replace (nth i l1 0) with (nth i (l1 ++ l2) 0).
  replace (nth j l2 0) with (nth (length l1 + j) (l1 ++ l2) 0).
  - apply nth_sorted_le_nat_120.
    + exact Hsorted.
    + rewrite app_length.
      lia.
  - rewrite app_nth2 by lia.
    replace (length l1 + j - length l1)%nat with j by lia.
    reflexivity.
  - rewrite app_nth1 by lia.
    reflexivity.
Qed.
Lemma problem_120_spec_of_sorted : forall input k output sorted_l,
  0 < k <= Zlength input ->
  k = Zlength output ->
  Zlength sorted_l = Zlength input ->
  sorted_int_list_by 1 sorted_l ->
  Permutation input sorted_l ->
  output = maximum_output_prefix sorted_l (Zlength input) k k ->
  problem_120_spec input k output.
Proof.
  intros input k output sorted_l Hk Hout_len Hsorted_len Hsorted Hperm Houtput.
  destruct Hk as [Hk_pos Hk_le].
  subst output.
  assert (Hsorted_list : Sorted Z.le sorted_l).
  {
    unfold sorted_int_list_by in Hsorted.
    simpl in Hsorted.
    exact Hsorted.
  }
  set (rest := sublist 0 (Zlength input - k) sorted_l).
  set (output := maximum_output_prefix sorted_l (Zlength input) k k).
  assert (Hsplit : sorted_l = rest ++ output).
  {
    subst rest output.
    unfold maximum_output_prefix.
    replace (Zlength input - k + k) with (Zlength input) by lia.
    rewrite <- (sublist_split 0 (Zlength input) (Zlength input - k) sorted_l).
    - symmetry. apply sublist_self.
      lia.
    - lia.
    - lia.
  }
  unfold problem_120_spec.
  repeat split.
  - subst output.
    rewrite maximum_output_prefix_Zlength by lia.
    lia.
  - apply (Sorted_app_right_120 rest).
    rewrite <- Hsplit.
    exact Hsorted_list.
  - exists rest.
    split.
    + eapply Permutation_trans.
      * apply Permutation_app_comm.
      * eapply Permutation_trans.
        -- rewrite <- Hsplit.
           reflexivity.
        -- apply Permutation_sym.
           exact Hperm.
    + intros x y Hx Hy.
      apply (Sorted_app_all_le_120 rest output); auto.
      rewrite <- Hsplit.
      exact Hsorted_list.
Qed.


Lemma proof_of_p120_maximum_entail_wit_1 : p120_maximum_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z).
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
Qed. 

Lemma proof_of_p120_maximum_entail_wit_2 : p120_maximum_entail_wit_2.
Proof.
  pre_process.
  Exists (tmp_l_2 ++ (Znth i input_l 0 :: nil)).
  entailer!.
  - rewrite copy_prefix_snoc by lia.
    subst tmp_l_2.
    reflexivity.
  - rewrite Zlength_app.
    rewrite Zlength_cons.
    rewrite Zlength_nil.
    lia.
Qed. 

Lemma proof_of_p120_maximum_entail_wit_3 : p120_maximum_entail_wit_3.
Proof.
  pre_process.
  replace i with arr_size_pre in * by lia.
  subst tmp_l.
  rewrite copy_prefix_full by lia.
  entailer!.
Qed. 

Lemma proof_of_p120_maximum_entail_wit_4 : p120_maximum_entail_wit_4.
Proof.
  pre_process.
  assert (sorted_full_l = sorted_l_2).
  {
    rewrite <- H5.
    symmetry.
    apply sublist_self.
    lia.
  }
  subst sorted_full_l.
  Exists sorted_l_2.
  entailer!.
Qed. 

Lemma proof_of_p120_maximum_entail_wit_5 : p120_maximum_entail_wit_5.
Proof.
  pre_process.
  Exists (@nil Z) sorted_l_2.
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
  - symmetry. apply maximum_output_prefix_nil.
Qed. 

Lemma proof_of_p120_maximum_entail_wit_6 : p120_maximum_entail_wit_6.
Proof.
  pre_process.
  Exists (output_l_2 ++ (Znth (arr_size_pre - k_pre + i) sorted_l_2 0 :: nil)) sorted_l_2.
  entailer!.
  - rewrite maximum_output_prefix_snoc by lia.
    subst output_l_2.
    replace (arr_size_pre - k_pre + i) with ((arr_size_pre - k_pre) + i) by lia.
    reflexivity.
  - rewrite Zlength_app.
    rewrite Zlength_cons.
    rewrite Zlength_nil.
    lia.
Qed. 

Lemma proof_of_p120_maximum_entail_wit_7 : p120_maximum_entail_wit_7.
Proof.
  pre_process.
  replace i with k_pre in * by lia.
  Exists output_l_2 sorted_l_2.
  subst output_l_2.
  assert (problem_120_spec input_l k_pre
            (maximum_output_prefix sorted_l_2 arr_size_pre k_pre k_pre)).
  {
    replace arr_size_pre with (Zlength input_l) by lia.
    apply problem_120_spec_of_sorted with (sorted_l := sorted_l_2); try assumption; try lia.
    - symmetry. apply maximum_output_prefix_Zlength; lia.
    - reflexivity.
  }
  rewrite IntArray.undef_seg_empty.
  sep_apply (IntArray.seg_to_full data 0 k_pre (maximum_output_prefix sorted_l_2 arr_size_pre k_pre k_pre)).
  replace (data + 0 * sizeof(INT)) with data by lia.
  replace (k_pre - 0) with k_pre by lia.
  entailer!.
Qed. 

Lemma proof_of_p120_maximum_return_wit_2 : p120_maximum_return_wit_2.
Proof.
  pre_process.
  replace k_pre with 0 in * by lia.
  Exists (@nil Z) retval_2.
  sep_apply IntArray_undef_full_0_to_full_nil.
  entailer!.
  - apply problem_120_spec_nil.
Qed. 

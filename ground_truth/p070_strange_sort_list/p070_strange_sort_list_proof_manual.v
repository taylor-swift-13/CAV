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
From SimpleC.EE.CAV.ground_truth_p070_strange_sort_list Require Import p070_strange_sort_list_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Arith.Arith.

Import naive_C_Rules.
Require Import p070_strange_sort_list.
Local Open Scope sac.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
From AUXLib Require Import ListLib.

Local Open Scope list_scope.

(* Proof helpers moved from p070_strange_sort_list.v so public contract files expose definitions only. *)

Lemma copy_prefix_Zlength : forall n input,
  0 <= n ->
  Zlength (copy_prefix n input) = n.
Proof.
  intros n input Hn.
  unfold copy_prefix.
  rewrite Zlength_correct.
  replace n with (Z.of_nat (Z.to_nat n)) at 2 by lia.
  revert input.
  induction (Z.to_nat n); intros; simpl; [reflexivity |].
  rewrite app_length.
  simpl.
  rewrite Nat2Z.inj_add.
  simpl.
  rewrite IHn0.
  lia.
Qed.
Lemma copy_prefix_0 : forall input,
  copy_prefix 0 input = [].
Proof.
  reflexivity.
Qed.
Lemma copy_prefix_snoc : forall i input,
  0 <= i ->
  copy_prefix (i + 1) input = copy_prefix i input ++ [Znth i input 0].
Proof.
  intros i input Hi.
  unfold copy_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.
Lemma sublist_snoc_Znth : forall (l : list Z) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0].
Proof.
  intros l i Hi.
  rewrite Zlength_correct in Hi.
  pose proof (sublist_split 0 (i + 1) i l ltac:(lia) ltac:(rewrite ?Zlength_correct; lia)) as Hsplit.
  rewrite Hsplit.
  rewrite (sublist_single 0 i l) by (rewrite ?Zlength_correct; lia).
  reflexivity.
Qed.
Lemma copy_prefix_eq_sublist_nat : forall n input,
  Z.of_nat n <= Zlength input ->
  copy_prefix (Z.of_nat n) input = sublist 0 (Z.of_nat n) input.
Proof.
  induction n as [| n IH]; intros input Hle.
  - reflexivity.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    rewrite copy_prefix_snoc by lia.
    rewrite sublist_snoc_Znth by lia.
    rewrite IH by lia.
    reflexivity.
Qed.
Lemma copy_prefix_eq_sublist : forall input i,
  0 <= i <= Zlength input ->
  copy_prefix i input = sublist 0 i input.
Proof.
  intros input i Hi.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  apply copy_prefix_eq_sublist_nat.
  lia.
Qed.
Lemma copy_prefix_full : forall input,
  copy_prefix (Zlength input) input = input.
Proof.
  intros input.
  pose proof (Zlength_nonneg input).
  rewrite copy_prefix_eq_sublist by lia.
  apply sublist_self.
  reflexivity.
Qed.
Lemma strange_output_prefix_Zlength : forall size i sorted_l,
  0 <= i ->
  Zlength (strange_output_prefix size i sorted_l) = i.
Proof.
  intros size i sorted_l Hi.
  unfold strange_output_prefix.
  rewrite Zlength_correct.
  replace i with (Z.of_nat (Z.to_nat i)) at 2 by lia.
  revert size sorted_l.
  induction (Z.to_nat i); intros; simpl; [reflexivity |].
  rewrite app_length.
  simpl.
  rewrite Nat2Z.inj_add.
  simpl.
  rewrite IHn.
  lia.
Qed.
Lemma strange_output_prefix_0 : forall size sorted_l,
  strange_output_prefix size 0 sorted_l = [].
Proof.
  reflexivity.
Qed.
Lemma strange_output_prefix_snoc : forall size i sorted_l,
  0 <= i ->
  strange_output_prefix size (i + 1) sorted_l =
  strange_output_prefix size i sorted_l ++ [Znth (strange_index size i) sorted_l 0].
Proof.
  intros size i sorted_l Hi.
  unfold strange_output_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.
Lemma strange_index_even : forall size i,
  Z.rem i 2 = 0 ->
  strange_index size i = i ÷ 2.
Proof.
  intros size i Hrem.
  unfold strange_index.
  rewrite Hrem.
  reflexivity.
Qed.
Lemma strange_index_odd : forall size i,
  Z.rem i 2 <> 0 ->
  strange_index size i = size - 1 - i ÷ 2.
Proof.
  intros size i Hrem.
  unfold strange_index.
  destruct (Z.eqb_spec (Z.rem i 2) 0); [contradiction | reflexivity].
Qed.
Lemma strange_output_full : forall size sorted_l,
  strange_output size sorted_l = strange_output_prefix size size sorted_l.
Proof.
  reflexivity.
Qed.
Lemma sorted_full_Znth : forall full_l sorted_l size idx,
  0 <= idx < size ->
  sublist 0 size full_l = sorted_l ->
  Znth idx full_l 0 = Znth idx sorted_l 0.
Proof.
  intros full_l sorted_l size idx Hidx Hsub.
  rewrite <- Hsub.
  rewrite Znth_sublist0 by lia.
  reflexivity.
Qed.
Lemma quot2_bounds : forall size i,
  0 <= size ->
  0 <= i ->
  i < size ->
  0 <= i ÷ 2 < size.
Proof.
  intros size i Hsize Hi Hlt.
  assert (Hq : i ÷ 2 = i / 2) by (apply Z.quot_div_nonneg; lia).
  rewrite Hq.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.
Lemma reverse_quot2_bounds : forall size i,
  0 <= size ->
  0 <= i ->
  i < size ->
  0 <= size - 1 - i ÷ 2 < size.
Proof.
  intros size i Hsize Hi Hlt.
  pose proof (quot2_bounds size i Hsize Hi Hlt) as [Hq0 Hqlt].
  split; lia.
Qed.


Lemma proof_of_p070_strange_sort_list_entail_wit_1 : p070_strange_sort_list_entail_wit_1.
Proof.
  pre_process.
  sep_apply IntArray.undef_full_to_undef_seg.
  change (copy_prefix 0 input_l) with (@nil Z).
  rewrite IntArray.seg_empty.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
Qed.

Lemma proof_of_p070_strange_sort_list_entail_wit_2 : p070_strange_sort_list_entail_wit_2.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  - rewrite copy_prefix_snoc by lia. reflexivity.
  - rewrite copy_prefix_Zlength by lia. lia.
Qed.

Lemma proof_of_p070_strange_sort_list_entail_wit_3 : p070_strange_sort_list_entail_wit_3.
Proof.
  pre_process.
  replace i with lst_size_pre in * by lia.
  assert (Hcopy : copy_prefix lst_size_pre input_l = input_l).
  { rewrite H5. apply copy_prefix_full. }
  rewrite Hcopy.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
Qed.

Lemma proof_of_p070_strange_sort_list_entail_wit_4 : p070_strange_sort_list_entail_wit_4.
Proof.
  pre_process.
  Exists sorted_full_l_2 sorted_l_2.
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  - intros Hlt. replace (0 ÷ 2) with 0 by reflexivity. split; lia.
  - intros Hlt. replace (0 ÷ 2) with 0 by reflexivity. split; lia.
Qed.

Lemma proof_of_p070_strange_sort_list_entail_wit_5_1 : p070_strange_sort_list_entail_wit_5_1.
Proof.
  pre_process.
  Exists sorted_full_l_2 sorted_l_2.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  - rewrite strange_output_prefix_snoc by lia.
    rewrite strange_index_even by assumption.
    rewrite (sorted_full_Znth sorted_full_l_2 sorted_l_2 lst_size_pre (i ÷ 2));
      [simpl_entail | lia | assumption].
  - rewrite strange_output_prefix_Zlength by lia. lia.
  - apply reverse_quot2_bounds; lia.
  - apply quot2_bounds; lia.
Qed.

Lemma proof_of_p070_strange_sort_list_entail_wit_5_2 : p070_strange_sort_list_entail_wit_5_2.
Proof.
  pre_process.
  Exists sorted_full_l_2 sorted_l_2.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  - rewrite strange_output_prefix_snoc by lia.
    rewrite strange_index_odd by assumption.
    rewrite (sorted_full_Znth sorted_full_l_2 sorted_l_2 lst_size_pre ((lst_size_pre - 1) - (i ÷ 2)));
      [simpl_entail | lia | assumption].
  - rewrite strange_output_prefix_Zlength by lia. lia.
  - apply reverse_quot2_bounds; lia.
  - apply quot2_bounds; lia.
Qed.

Lemma proof_of_p070_strange_sort_list_return_wit_1 : p070_strange_sort_list_return_wit_1.
Proof.
  pre_process.
  Exists (strange_output_prefix lst_size_pre i sorted_l) data_2.
  replace i with lst_size_pre in * by lia.
  sep_apply (IntArray.seg_to_full data_2 0 lst_size_pre (strange_output_prefix lst_size_pre lst_size_pre sorted_l)).
  replace (data_2 + 0 * sizeof(INT)) with data_2 by lia.
  replace (lst_size_pre - 0) with lst_size_pre by lia.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
Qed.

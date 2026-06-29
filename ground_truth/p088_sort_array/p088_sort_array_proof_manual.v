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
From SimpleC.EE.CAV.ground_truth_p088_sort_array Require Import p088_sort_array_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import List.
Require Import Arith.
Require Import Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p088_sort_array.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p088_sort_array.v so public contract files expose definitions only. *)

Lemma reverse_loop_0 : forall size l,
  reverse_loop size 0 l = l.
Proof.
  reflexivity.
Qed.
Lemma replace_Znth_length_local {A : Type} :
  forall (l : list A) n a,
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros l n a.
  unfold replace_Znth.
  remember (Z.to_nat n) as k; clear Heqk.
  revert k; induction l; intros k.
  - destruct k; simpl; reflexivity.
  - destruct k; simpl; repeat rewrite Zlength_cons; try rewrite IHl; lia.
Qed.
Lemma copy_prefix_Zlength : forall n input,
  0 <= n ->
  Zlength (copy_prefix n input) = n.
Proof.
  intros n input Hn.
  unfold copy_prefix.
  rewrite Zlength_correct.
  replace n with (Z.of_nat (Z.to_nat n)) at 2 by lia.
  revert input.
  induction (Z.to_nat n); intros; simpl.
  - reflexivity.
  - rewrite app_length.
    simpl.
    rewrite Nat2Z.inj_add.
    simpl.
    rewrite IHn0.
    lia.
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
  pose proof (sublist_split 0 (i + 1) i l ltac:(lia) ltac:(lia)) as Hsplit.
  rewrite Hsplit.
  rewrite (sublist_single 0 i l) by lia.
  reflexivity.
Qed.
Lemma copy_prefix_eq_sublist_nat : forall n input,
  Z.of_nat n <= Zlength input ->
  copy_prefix (Z.of_nat n) input = sublist 0 (Z.of_nat n) input.
Proof.
  induction n; intros input Hle.
  - reflexivity.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    rewrite copy_prefix_snoc by lia.
    rewrite sublist_snoc_Znth by lia.
    rewrite IHn by lia.
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
Lemma reverse_step_Zlength : forall size i l,
  Zlength (reverse_step size i l) = Zlength l.
Proof.
  intros.
  unfold reverse_step.
  rewrite (@replace_Znth_length_local Z
             (replace_Znth i (Znth (size - 1 - i) l 0) l)
             (size - 1 - i) (Znth i l 0)).
  rewrite (@replace_Znth_length_local Z l i (Znth (size - 1 - i) l 0)).
  reflexivity.
Qed.
Lemma reverse_loop_Zlength : forall size i l,
  0 <= i ->
  Zlength (reverse_loop size i l) = Zlength l.
Proof.
  intros size i l Hi.
  unfold reverse_loop.
  replace i with (Z.of_nat (Z.to_nat i)) at 2 by lia.
  revert size l.
  induction (Z.to_nat i); intros; simpl.
  - reflexivity.
  - rewrite reverse_step_Zlength.
    rewrite IHn.
    reflexivity.
Qed.
Lemma reverse_loop_snoc : forall size i l,
  0 <= i ->
  reverse_loop size (i + 1) l =
  reverse_step size i (reverse_loop size i l).
Proof.
  intros size i l Hi.
  unfold reverse_loop.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.
Lemma problem_88_spec_nil :
  problem_88_spec [] [].
Proof.
  unfold problem_88_spec.
  split; constructor.
Qed.


Lemma proof_of_p088_sort_array_safety_wit_6 : p088_sort_array_safety_wit_6.
Proof.
  pre_process.
  match goal with
  | H : sort_array_input_range input_l |- _ => destruct H as [Hrange Hsum]
  end.
  entailer!.
  - pose proof (Hrange 0 ltac:(lia)).
    pose proof (Hrange (array_size_pre - 1) ltac:(lia)).
    lia.
  - rewrite H8.
    apply Hsum. lia.
Qed. 

Lemma proof_of_p088_sort_array_entail_wit_1 : p088_sort_array_entail_wit_1.
Proof.
  pre_process.
  sep_apply IntArray.undef_full_to_undef_seg.
  change (copy_prefix 0 input_l) with (@nil Z).
  rewrite IntArray.seg_empty.
  entailer!.
Qed. 

Lemma proof_of_p088_sort_array_entail_wit_2 : p088_sort_array_entail_wit_2.
Proof.
  pre_process.
  rewrite copy_prefix_snoc by lia.
  entailer!.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  rewrite <- H9.
  lia.
Qed. 

Lemma proof_of_p088_sort_array_entail_wit_3 : p088_sort_array_entail_wit_3.
Proof.
  pre_process.
  replace i with array_size_pre in * by lia.
  assert (Hcopy : copy_prefix array_size_pre input_l = input_l).
  {
    match goal with
    | H : array_size_pre = Zlength input_l |- _ =>
        rewrite H; apply copy_prefix_full
    end.
  }
  rewrite Hcopy.
  rewrite (IntArray.undef_seg_empty data array_size_pre).
  sep_apply (IntArray.seg_to_full data 0 array_size_pre input_l).
  replace (data + 0 * sizeof(INT)) with data by lia.
  replace (array_size_pre - 0) with array_size_pre by lia.
  entailer!.
Qed. 

Lemma proof_of_p088_sort_array_entail_wit_4 : p088_sort_array_entail_wit_4.
Proof.
  pre_process.
  Exists sorted_l_2.
  rewrite reverse_loop_0.
  assert (Hspec : problem_88_spec input_l
                    (reverse_loop array_size_pre (array_size_pre ÷ 2) sorted_l_2)).
  { apply H4. split; assumption. }
  assert (Hq : 0 <= array_size_pre ÷ 2).
  {
    assert (Hquot : array_size_pre ÷ 2 = array_size_pre / 2) by
      (apply Z.quot_div_nonneg; lia).
    rewrite Hquot.
    apply Z.div_pos; lia.
  }
  assert (Hb1 : 0 < array_size_pre ÷ 2 -> 0 <= 0 < array_size_pre).
  { intros; lia. }
  assert (Hb2 : 0 < array_size_pre ÷ 2 ->
                0 <= array_size_pre - 1 - 0 < array_size_pre).
  { intros; lia. }
  entailer!.
Qed. 

Lemma proof_of_p088_sort_array_entail_wit_5 : p088_sort_array_entail_wit_5.
Proof.
  pre_process.
  Exists sorted_l_2.
  rewrite reverse_loop_snoc by lia.
  unfold reverse_step.
  assert (Hqle : array_size_pre ÷ 2 <= array_size_pre).
  {
    assert (Hquot : array_size_pre ÷ 2 = array_size_pre / 2) by
      (apply Z.quot_div_nonneg; lia).
    rewrite Hquot.
    apply Z.div_le_upper_bound; lia.
  }
  assert (Hb1 : i + 1 < array_size_pre ÷ 2 ->
                0 <= i + 1 < array_size_pre).
  { intros; lia. }
  assert (Hb2 : i + 1 < array_size_pre ÷ 2 ->
                0 <= array_size_pre - 1 - (i + 1) < array_size_pre).
  { intros; lia. }
  assert (Hlen : array_size_pre =
                 Zlength (reverse_loop array_size_pre (i + 1) sorted_l_2)).
  { rewrite reverse_loop_Zlength by lia. lia. }
  assert (Hlen_step :
            array_size_pre =
            Zlength
              (replace_Znth (array_size_pre - 1 - i)
                 (Znth i (reverse_loop array_size_pre i sorted_l_2) 0)
                 (replace_Znth i
                    (Znth (array_size_pre - 1 - i)
                       (reverse_loop array_size_pre i sorted_l_2) 0)
                    (reverse_loop array_size_pre i sorted_l_2)))).
  {
    repeat rewrite replace_Znth_length_local.
    exact H16.
  }
  entailer!.
Qed. 

Lemma proof_of_p088_sort_array_return_wit_1 : p088_sort_array_return_wit_1.
Proof.
  pre_process.
  replace i with (array_size_pre ÷ 2) in * by lia.
  Exists (reverse_loop array_size_pre (array_size_pre ÷ 2) sorted_l) data_2.
  entailer!.
Qed.

Lemma proof_of_p088_sort_array_return_wit_2 : p088_sort_array_return_wit_2.
Proof.
  pre_process.
  Exists sorted_l data_2.
  entailer!.
Qed. 

Lemma proof_of_p088_sort_array_return_wit_3 : p088_sort_array_return_wit_3.
Proof.
  pre_process.
  assert (Hnil : input_l = (@nil Z)).
  {
    apply Zlength_nil_inv.
    lia.
  }
  subst array_size_pre.
  subst input_l.
  Exists (@nil Z) retval_2.
  rewrite (IntArray.undef_full_empty retval_2).
  rewrite (IntArray.full_empty retval_2 0).
  entailer!.
  apply problem_88_spec_nil.
Qed. 

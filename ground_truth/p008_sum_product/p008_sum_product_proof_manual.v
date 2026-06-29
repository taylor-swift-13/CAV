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
From SimpleC.EE.CAV.ground_truth_p008_sum_product Require Import p008_sum_product_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Require Import Coq.micromega.Lia.

Import naive_C_Rules.
Require Import p008_sum_product.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p008_sum_product.v so public contract files expose definitions only. *)

Lemma prefix_sum_snoc : forall l i,
  0 <= i < Zlength l ->
  prefix_sum l (i + 1) = prefix_sum l i + Znth i l 0.
Proof.
  intros.
  unfold prefix_sum.
  rewrite (sublist_split 0 (i + 1) i l) by (try rewrite Zlength_correct in *; lia).
  rewrite (sublist_single 0 i l) by lia.
  rewrite fold_left_app.
  simpl.
  lia.
Qed.
Lemma prefix_product_snoc : forall l i,
  0 <= i < Zlength l ->
  prefix_product l (i + 1) = prefix_product l i * Znth i l 0.
Proof.
  intros.
  unfold prefix_product.
  rewrite (sublist_split 0 (i + 1) i l) by (try rewrite Zlength_correct in *; lia).
  rewrite (sublist_single 0 i l) by lia.
  rewrite fold_left_app.
  simpl.
  lia.
Qed.
Lemma problem_8_spec_of_prefix_full : forall l n,
  n = Zlength l ->
  problem_8_spec l (prefix_sum l n) (prefix_product l n).
Proof.
  intros.
  unfold problem_8_spec, prefix_sum, prefix_product.
  subst n.
  rewrite sublist_self by reflexivity.
  auto.
Qed.


Lemma proof_of_p008_sum_product_safety_wit_5 : p008_sum_product_safety_wit_5.
Proof.
  pre_process.
  prop_apply (IntArray.full_length numbers0). Intros.
  subst sum.
  assert (Hidx: 0 <= i + 1 <= numbers_size0) by lia.
  match goal with
  | H: prefix_sum_product_int_range lv numbers_size0 |- _ =>
      pose proof (H (i + 1) Hidx) as [Hsum _]
  end.
  rewrite <- prefix_sum_snoc by (rewrite Zlength_correct; lia).
  entailer!.
Qed.

Lemma proof_of_p008_sum_product_safety_wit_6 : p008_sum_product_safety_wit_6.
Proof.
  pre_process.
  prop_apply (IntArray.full_length numbers0). Intros.
  subst product.
  assert (Hidx: 0 <= i + 1 <= numbers_size0) by lia.
  match goal with
  | H: prefix_sum_product_int_range lv numbers_size0 |- _ =>
      pose proof (H (i + 1) Hidx) as [_ Hprod]
  end.
  rewrite <- prefix_product_snoc by (rewrite Zlength_correct; lia).
  entailer!.
Qed.

Lemma proof_of_p008_sum_product_entail_wit_1 : p008_sum_product_entail_wit_1.
Proof.
  pre_process.
  subst.
  unfold prefix_sum, prefix_product.
  replace (sublist 0 0 lv) with (@nil Z) by reflexivity.
  simpl.
  entailer!.
Qed.

Lemma proof_of_p008_sum_product_entail_wit_2 : p008_sum_product_entail_wit_2.
Proof.
  pre_process.
  prop_apply (IntArray.full_length numbers0). Intros.
  subst sum product.
  rewrite <- prefix_sum_snoc by (rewrite Zlength_correct; lia).
  rewrite <- prefix_product_snoc by (rewrite Zlength_correct; lia).
  entailer!.
Qed.

Lemma proof_of_p008_sum_product_return_wit_1 : p008_sum_product_return_wit_1.
Proof.
  pre_process.
  prop_apply (IntArray.full_length numbers0). Intros.
  assert (Hi: i = numbers_size0) by lia.
  subst i.
  Exists (prefix_sum lv numbers_size0) (prefix_product lv numbers_size0).
  sep_apply (IntArray.seg_single out 1 product).
  sep_apply (IntArray.seg_single out 0 sum).
  sep_apply (IntArray.seg_merge_to_full out 0 1 2 (sum :: nil) (product :: nil)); [ | lia].
  entailer!.
  - replace (out + 0 * sizeof (INT)) with out by lia.
    replace (2 - 0) with 2 by lia.
    subst sum product.
    simpl.
    entailer!.
  - subst sum product.
    apply problem_8_spec_of_prefix_full.
    rewrite Zlength_correct.
    lia.
Qed.

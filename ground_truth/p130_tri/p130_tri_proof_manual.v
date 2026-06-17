Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p130_tri Require Import p130_tri_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p130_tri.
Local Open Scope sac.

Lemma proof_of_p130_tri_safety_wit_14 : p130_tri_safety_wit_14.
Proof.
  pre_process.
  pose proof (tri_even_expr_range n0 i H6 ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_p130_tri_safety_wit_18 : p130_tri_safety_wit_18.
Proof.
  pre_process.
  rewrite !tri_sequence_sublist_Znth by lia.
  pose proof (tri_odd_expr_range n0 i H6 ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_p130_tri_safety_wit_21 : p130_tri_safety_wit_21.
Proof.
  pre_process.
  rewrite !tri_sequence_sublist_Znth by lia.
  pose proof (tri_odd_expr_partial_range_2 n0 i H6 ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_p130_tri_safety_wit_22 : p130_tri_safety_wit_22.
Proof.
  pre_process.
  rewrite !tri_sequence_sublist_Znth by lia.
  pose proof (tri_odd_expr_partial_range_1 n0 i H6 ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_p130_tri_entail_wit_1 : p130_tri_entail_wit_1.
Proof.
  pre_process.
  subst.
  rewrite tri_sequence_Zlength by lia.
  rewrite tri_sequence_sublist_2 by lia.
  sep_apply (IntArray.seg_single retval_2 1 3).
  sep_apply (IntArray.seg_single retval_2 0 1).
  sep_apply (IntArray.seg_merge_to_seg retval_2 0 1 2); [ | lia].
  entailer!.
Qed.

Lemma proof_of_p130_tri_entail_wit_2_1 : p130_tri_entail_wit_2_1.
Proof.
  pre_process.
  rewrite tri_sequence_even_snoc by lia.
  entailer!.
Qed.

Lemma proof_of_p130_tri_entail_wit_2_2 : p130_tri_entail_wit_2_2.
Proof.
  pre_process.
  rewrite tri_sequence_odd_snoc by lia.
  entailer!.
Qed.

Lemma proof_of_p130_tri_return_wit_1 : p130_tri_return_wit_1.
Proof.
  pre_process.
  replace i with (n0 + 1) in * by lia.
  Exists (tri_sequence n0) (n0 + 1) data_2.
  entailer!.
  - rewrite sublist_self by (rewrite tri_sequence_Zlength by lia; lia).
    sep_apply (IntArray.seg_to_full data_2 0 (n0 + 1)).
    replace (data_2 + 0 * sizeof (INT)) with data_2 by lia.
    replace (n0 + 1 - 0) with (n0 + 1) by lia.
    rewrite (IntArray.undef_seg_empty data_2 (n0 + 1)).
    entailer!.
  - apply tri_sequence_spec.
    lia.
Qed.

Lemma proof_of_p130_tri_return_wit_2 : p130_tri_return_wit_2.
Proof.
  pre_process.
  Exists (tri_sequence n0) (n0 + 1) retval_2.
  entailer!.
  - replace n0 with 0 in * by lia.
    subst n_pre.
    replace (tri_sequence 0) with (1 :: nil) by reflexivity.
    sep_apply (IntArray.seg_single retval_2 0 1).
    sep_apply (IntArray.seg_to_full retval_2 0 1).
    replace (retval_2 + 0 * sizeof (INT)) with retval_2 by lia.
    replace (1 - 0) with 1 by lia.
    rewrite (IntArray.undef_seg_empty retval_2 1).
    entailer!.
  - apply tri_sequence_spec.
    lia.
  - rewrite tri_sequence_Zlength by lia.
    lia.
Qed.

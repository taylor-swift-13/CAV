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
From SimpleC.EE.CAV.verify_20260615_hil_xizi_single_link_remove_node Require Import xizi_single_link_remove_node_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import xizi_single_link_lib.
Local Open Scope sac.

Lemma proof_of_xizi_single_link_remove_node_entail_wit_1 : xizi_single_link_remove_node_entail_wit_1.
Proof.
  pre_process.
  sep_apply xizi_sll_to_target_not_same; [ | tauto ].
  Intros d next l0.
  Exists next (@nil Z).
  Exists d l0 l0 d.
  simpl xizi_sllseg.
  simpl app.
  entailer!.
Qed.

Lemma proof_of_xizi_single_link_remove_node_entail_wit_2 : xizi_single_link_remove_node_entail_wit_2.
Proof.
  pre_process.
  sep_apply xizi_sll_to_target_not_same; [ | tauto ].
  Intros d next l0.
  pose (l1_new := l1_2 ++ (d_3 :: nil)).
  Exists next l1_new.
  Exists d l0.
  Exists l0_2 d_4.
  entailer!.
  - sep_apply (xizi_sllseg_len1 node d_3 next_2); [ | tauto ].
    sep_apply (xizi_sllseg_sllseg linklist_pre node next_2 l1_2 (d_3 :: nil)).
    entailer!.
  - subst l1_new.
    match goal with
    | Hsplit : l_before = app l1_2 (d_3 :: l2_2),
      Htail : l2_2 = d :: l0 |- _ =>
        rewrite Hsplit; rewrite Htail
    end.
    rewrite <- app_assoc.
    simpl.
    reflexivity.
Qed.

Lemma proof_of_xizi_single_link_remove_node_entail_wit_3_1 : xizi_single_link_remove_node_entail_wit_3_1.
Proof.
  pre_process.
  subst next.
  sep_apply xizi_sll_to_target_zero_nonzero; [ | tauto ].
  entailer!.
Qed.

Lemma proof_of_xizi_single_link_remove_node_entail_wit_3_2 : xizi_single_link_remove_node_entail_wit_3_2.
Proof.
  pre_process.
  subst next.
  sep_apply xizi_sll_to_target_same.
  Intros.
  subst l2.
  Exists linklist_node_pre l1_2 d_2.
  entailer!.
Qed.

Lemma proof_of_xizi_single_link_remove_node_return_wit_1 : xizi_single_link_remove_node_return_wit_1.
Proof.
  pre_process.
  subst node_node_next.
  replace (app l_before l_after) with (l1 ++ d :: l_after).
  - sep_apply (xizi_sll_cons node d target_next l_after); [ | tauto ].
    sep_apply (xizi_sllseg_sll linklist_pre node l1 (d :: l_after)).
    entailer!.
  - match goal with
    | Hsplit : l_before = app l1 (d :: nil) |- _ =>
        rewrite Hsplit
    end.
    rewrite <- app_assoc.
    simpl.
    reflexivity.
Qed.

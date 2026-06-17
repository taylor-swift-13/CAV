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
From SimpleC.EE.CAV.verify_20260615_hil_xizi_single_link_append Require Import xizi_single_link_append_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import ListNotations.
Import naive_C_Rules.
Require Import xizi_single_link_lib.
Local Open Scope sac.

Lemma proof_of_xizi_single_link_append_safety_wit_1 : xizi_single_link_append_safety_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_xizi_single_link_append_entail_wit_1 : xizi_single_link_append_entail_wit_1.
Proof.
  pre_process.
  sep_apply xizi_sll_not_zero; [ | tauto ].
  Intros d next l0.
  Exists next.
  Exists (@nil Z).
  Exists d.
  Exists l0.
  Exists l0.
  Exists d.
  simpl xizi_sllseg.
  entailer!.
Qed.

Lemma proof_of_xizi_single_link_append_entail_wit_2 : xizi_single_link_append_entail_wit_2.
Proof.
  pre_process.
  sep_apply xizi_sll_not_zero; [ | tauto ].
  Intros dnext next lnext.
  Exists next.
  Exists (l1a_2 ++ [d_3]).
  Exists dnext.
  Exists lnext.
  Exists l0_2.
  Exists d_4.
  entailer!.
  - sep_apply (xizi_sllseg_len1 node d_3 next_2); [ | tauto ].
    sep_apply (xizi_sllseg_sllseg linklist_pre node next_2 l1a_2 [d_3]).
    entailer!.
  - subst l1b_2.
    rewrite <- app_assoc.
    simpl.
    exact H.
Qed.

Lemma proof_of_xizi_single_link_append_return_wit_1 : xizi_single_link_append_return_wit_1.
Proof.
  pre_process.
  subst next.
  sep_apply (xizi_sll_zero 0 l1b); [ | reflexivity ].
  Intros.
  subst l1b.
  subst l.
  assert (Hln : linklist_node_pre <> NULL) by tauto.
  assert (Hz : 0 = NULL) by reflexivity.
  assert (Hnode : node <> NULL) by tauto.
  sep_apply (xizi_sll_len1 linklist_node_pre 0 0 Hln Hz).
  sep_apply (xizi_sll_cons node d linklist_node_pre [0] Hnode).
  sep_apply (xizi_sllseg_sll linklist_pre node l1a [d; 0]).
  rewrite <- app_assoc.
  simpl.
  entailer!.
Qed.

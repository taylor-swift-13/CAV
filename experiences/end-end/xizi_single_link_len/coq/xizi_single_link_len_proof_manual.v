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
From SimpleC.EE.CAV.verify_20260615_hil_xizi_single_link_len Require Import xizi_single_link_len_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import xizi_single_link_lib.
Local Open Scope sac.

Lemma proof_of_xizi_single_link_len_entail_wit_1 : xizi_single_link_len_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z) l.
  simpl xizi_sllseg.
  simpl app.
  simpl Zlength.
  entailer!.
Qed.

Lemma proof_of_xizi_single_link_len_entail_wit_2 : xizi_single_link_len_entail_wit_2.
Proof.
  pre_process.
  subst l2_2.
  Exists (l1_2 ++ (d :: nil)) l0.
  entailer!.
  - sep_apply (xizi_sllseg_len1 tmp_list d q); [ | tauto ].
    sep_apply (xizi_sllseg_sllseg first tmp_list q l1_2 (d :: nil)).
    entailer!.
  - rewrite Zlength_app.
    rewrite Zlength_cons.
    rewrite Zlength_nil.
    match goal with
    | Hlen : length = Zlength l1_2 |- _ => rewrite Hlen
    end.
    apply unsigned_last_nbits_eq.
    let Hb := fresh "Hb" in
    match goal with
    | Hsplit : l = app l1_2 (d :: l0),
      Hbound : Zlength l <= UINT_MAX |- _ =>
        pose proof Hbound as Hb;
        rewrite Hsplit in Hb;
        rewrite Zlength_app in Hb;
        rewrite Zlength_cons in Hb
    end.
    pose proof (Zlength_nonneg l1_2).
    pose proof (Zlength_nonneg l0).
    lia.
  - match goal with
    | Hsplit : l = app l1_2 (d :: l0) |- _ =>
        rewrite Hsplit
    end.
    rewrite <- app_assoc.
    simpl.
    reflexivity.
Qed.

Lemma proof_of_xizi_single_link_len_return_wit_1 : xizi_single_link_len_return_wit_1.
Proof.
  pre_process.
  subst tmp_list.
  sep_apply (xizi_sll_zero 0 l2); [ | reflexivity ].
  Intros.
  subst l2.
  sep_apply (xizi_sllseg_0_sll first l1).
  rewrite app_nil_r in H0.
  subst l.
  entailer!.
Qed.

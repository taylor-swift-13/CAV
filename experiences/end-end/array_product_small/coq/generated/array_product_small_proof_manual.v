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
From SimpleC.EE.CAV.verify_20260605_004203v_array_product_small Require Import array_product_small_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_product_small.
Local Open Scope sac.

Lemma product_app :
  forall xs ys : list Z,
    product (xs ++ ys) = product xs * product ys.
Proof.
  induction xs.
  - intros. simpl. destruct (product ys); reflexivity.
  - intros. simpl. rewrite IHxs. ring.
Qed.

Lemma product_sublist_succ :
  forall l i,
    0 <= i < Zlength l ->
    product (sublist 0 (i + 1) l) = product (sublist 0 i l) * Znth i l 0.
Proof.
  intros l i Hi.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite product_app.
  rewrite (sublist_single 0 i l) by lia.
  simpl. ring.
Qed.

Lemma proof_of_array_product_small_safety_wit_3 : array_product_small_safety_wit_3.
Proof.
  pre_process.
  entailer!.
  - pose proof (H5 (i + 1)) as Hbound.
    assert (0 <= i + 1 <= n_pre) as Hrange by lia.
    specialize (Hbound Hrange).
    rewrite H2.
    rewrite <- (product_sublist_succ l i) by lia.
    lia.
  - pose proof (H5 (i + 1)) as Hbound.
    assert (0 <= i + 1 <= n_pre) as Hrange by lia.
    specialize (Hbound Hrange).
    rewrite H2.
    rewrite <- (product_sublist_succ l i) by lia.
    lia.
Qed.

Lemma proof_of_array_product_small_entail_wit_1 : array_product_small_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_array_product_small_entail_wit_2 : array_product_small_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  rewrite H2.
  rewrite <- (product_sublist_succ l i) by lia.
  reflexivity.
Qed.

Lemma proof_of_array_product_small_return_wit_1 : array_product_small_return_wit_1.
Proof.
  pre_process.
  entailer!.
  assert (i = n_pre) by lia.
  subst i.
  rewrite H2.
  rewrite (sublist_self l n_pre) by auto.
  reflexivity.
Qed.

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
From SimpleC.EE.CAV.verify_20260605_000102v_array_count_nonzero Require Import array_count_nonzero_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_count_nonzero.
Local Open Scope sac.

Lemma array_count_nonzero_spec_app :
  forall l1 l2,
    array_count_nonzero_spec (l1 ++ l2) =
    array_count_nonzero_spec l1 + array_count_nonzero_spec l2.
Proof.
  induction l1.
  - intros. simpl. lia.
  - intros. simpl. destruct (Z.eq_dec a 0).
    + rewrite IHl1. lia.
    + rewrite IHl1. lia.
Qed.

Lemma array_count_nonzero_spec_prefix_succ :
  forall l i,
    0 <= i < Zlength l ->
    array_count_nonzero_spec (sublist 0 (i + 1) l) =
    array_count_nonzero_spec (sublist 0 i l) +
    (if Z.eq_dec (Znth i l 0) 0 then 0 else 1).
Proof.
  intros.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite array_count_nonzero_spec_app.
  rewrite (sublist_single 0 i l) by lia.
  simpl.
  destruct (Z.eq_dec (Znth i l 0) 0); lia.
Qed.

Lemma proof_of_array_count_nonzero_entail_wit_2 : array_count_nonzero_entail_wit_2.
Proof.
  pre_process.
Qed.

Lemma proof_of_array_count_nonzero_entail_wit_3_1 : array_count_nonzero_entail_wit_3_1.
Proof.
  pre_process.
  entailer!.
  repeat split; try lia.
  rewrite array_count_nonzero_spec_prefix_succ by lia.
  match goal with
  | H : count = array_count_nonzero_spec (sublist 0 i l) |- _ =>
      rewrite H
  end.
  destruct (Z.eq_dec (Znth i l 0) 0); lia.
Qed.

Lemma proof_of_array_count_nonzero_entail_wit_3_2 : array_count_nonzero_entail_wit_3_2.
Proof.
  pre_process.
  entailer!.
  repeat split; try lia.
  rewrite array_count_nonzero_spec_prefix_succ by lia.
  match goal with
  | H : count = array_count_nonzero_spec (sublist 0 i l) |- _ =>
      rewrite H
  end.
  destruct (Z.eq_dec (Znth i l 0) 0); lia.
Qed.

Lemma proof_of_array_count_nonzero_return_wit_1 : array_count_nonzero_return_wit_1.
Proof.
  pre_process.
  entailer!.
  assert (i = n_pre) by lia.
  match goal with
  | H : count = array_count_nonzero_spec (sublist 0 i l) |- _ =>
      rewrite H
  end.
  subst i.
  rewrite sublist_self by lia.
  reflexivity.
Qed.

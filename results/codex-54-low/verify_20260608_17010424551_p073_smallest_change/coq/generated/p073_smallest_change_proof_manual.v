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
From SimpleC.EE.CAV.verify_20260608_17010424551_p073_smallest_change Require Import p073_smallest_change_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p073_smallest_change.
Local Open Scope sac.

Lemma proof_of_p073_smallest_change_safety_wit_17 : p073_smallest_change_safety_wit_17.
Proof.
  unfold p073_smallest_change_safety_wit_17.
  intros.
  Intros.
  assert (arr_size = arr_size_pre) by entailer!.
  entailer!.
  unfold smallest_change_int_range in H14.
  specialize (H14 i H4).
  assert (2 * i < Zlength lv) by lia.
  specialize (H14 H16).
  lia.
Qed.

Lemma proof_of_p073_smallest_change_entail_wit_1 : p073_smallest_change_entail_wit_1.
Proof.
  unfold p073_smallest_change_entail_wit_1.
  intros.
  Intros.
  entailer!.
  unfold count_half_mismatches_upto.
  simpl.
  lia.
Qed.

Lemma proof_of_p073_smallest_change_entail_wit_2_1 : p073_smallest_change_entail_wit_2_1.
Proof.
  unfold p073_smallest_change_entail_wit_2_1.
  intros.
  Intros.
  entailer!.
  subst out.
  unfold count_half_mismatches_upto.
  rewrite Z2Nat.inj_add by lia.
  replace (Z.to_nat 1) with 1%nat by reflexivity.
  simpl.
  rewrite Z.eqb_neq in H.
  rewrite H.
  lia.
Qed.

Lemma proof_of_p073_smallest_change_entail_wit_2_2 : p073_smallest_change_entail_wit_2_2.
Proof.
  unfold p073_smallest_change_entail_wit_2_2.
  intros.
  Intros.
  entailer!.
  subst out.
  unfold count_half_mismatches_upto.
  rewrite Z2Nat.inj_add by lia.
  replace (Z.to_nat 1) with 1%nat by reflexivity.
  simpl.
  rewrite Z.eqb_eq in H.
  rewrite H.
  lia.
Qed.

Lemma proof_of_p073_smallest_change_return_wit_1 : p073_smallest_change_return_wit_1.
Proof.
  unfold p073_smallest_change_return_wit_1.
  intros.
  Intros.
  assert (arr = arr_pre) by entailer!.
  assert (arr_size = arr_size_pre) by entailer!.
  entailer!.
  unfold problem_73_spec.
  subst.
  f_equal.
  lia.
Qed.

Lemma proof_of_p073_smallest_change_return_wit_2 : p073_smallest_change_return_wit_2.
Proof.
  unfold p073_smallest_change_return_wit_2.
  intros.
  Intros.
  lia.
Qed.

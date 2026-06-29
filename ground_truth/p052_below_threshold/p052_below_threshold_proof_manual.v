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
From SimpleC.EE.CAV.ground_truth_p052_below_threshold Require Import p052_below_threshold_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p052_below_threshold.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p052_below_threshold.v so public contract files expose definitions only. *)

Lemma problem_52_spec_false_of_counter : forall l n t i,
  Zlength l = n ->
  0 <= i < n ->
  Znth i l 0 >= t ->
  problem_52_spec l t false.
Proof.
  intros l n t i Hlen Hi Hge.
  unfold problem_52_spec.
  split; intro H.
  - specialize (H i).
    assert (0 <= i < Zlength l) by lia.
    specialize (H H0).
    lia.
  - discriminate H.
Qed.
Lemma problem_52_spec_true_of_all_below : forall l n t,
  Zlength l = n ->
  (forall k, 0 <= k < n -> Znth k l 0 < t) ->
  problem_52_spec l t true.
Proof.
  intros l n t Hlen Hall.
  unfold problem_52_spec.
  split.
  - intros _. reflexivity.
  - intros _ k Hk.
    apply Hall.
    lia.
Qed.


Lemma proof_of_p052_below_threshold_entail_wit_2 : p052_below_threshold_entail_wit_2.
Proof.
  pre_process.
  andp_cancel; auto; try lia.
  intros k Hk.
  assert (k < i \/ k = i) as [Hlt | ->] by lia.
  - match goal with
    | H: forall k, 0 <= k < i -> Znth k input_l 0 < t_pre |- _ =>
        apply H; lia
    end.
  - assumption.
Qed.

Lemma proof_of_p052_below_threshold_return_wit_1 : p052_below_threshold_return_wit_1.
Proof.
  pre_process.
  prop_apply (IntArray.full_Zlength l_pre). Intros.
  Right.
  andp_cancel; auto; try lia.
  apply problem_52_spec_true_of_all_below with (n := l_size_pre); auto.
  intros k Hk.
  match goal with
  | H: forall k, 0 <= k < i -> Znth k input_l 0 < t_pre |- _ =>
      apply H; lia
  end.
Qed.

Lemma proof_of_p052_below_threshold_return_wit_2 : p052_below_threshold_return_wit_2.
Proof.
  pre_process.
  prop_apply (IntArray.full_Zlength l_pre). Intros.
  Left.
  andp_cancel; auto; try lia.
  apply problem_52_spec_false_of_counter with (n := l_size_pre) (i := i);
    auto; lia.
Qed.

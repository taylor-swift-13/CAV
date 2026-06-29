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
From SimpleC.EE.CAV.ground_truth_p043_pairs_sum_to_zero Require Import p043_pairs_sum_to_zero_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p043_pairs_sum_to_zero.
Local Open Scope sac.
Require Import Coq.micromega.Lia.

Local Open Scope list_scope.

(* Proof helpers moved from p043_pairs_sum_to_zero.v so public contract files expose definitions only. *)

Lemma scanned_i_init :
  forall l n, scanned_i l n 0.
Proof.
  unfold scanned_i.
  intros.
  lia.
Qed.
Lemma scanned_j_init :
  forall l n i,
    scanned_i l n i ->
    scanned_j l n i (i + 1).
Proof.
  unfold scanned_j.
  intros l n i Hscan.
  split; [exact Hscan |].
  intros q Hiq _ Hq Hpair.
  lia.
Qed.
Lemma scanned_j_step :
  forall l n i j,
    scanned_j l n i j ->
    ~ pair_sum_zero l i j ->
    scanned_j l n i (j + 1).
Proof.
  unfold scanned_j.
  intros l n i j [Hscan_i Hscan_j] Hneq.
  split; [exact Hscan_i |].
  intros q Hiq Hqn Hq.
  assert (q < j \/ q = j) by lia.
  destruct H as [Hlt | Heq].
  - apply Hscan_j; lia.
  - subst q; exact Hneq.
Qed.
Lemma scanned_i_step :
  forall l n i j,
    j = n ->
    scanned_j l n i j ->
    scanned_i l n (i + 1).
Proof.
  unfold scanned_i, scanned_j.
  intros l n i j Hjn [Hscan_i Hscan_j].
  subst j.
  intros p q Hp Hqn Hp_lt.
  assert (p < i \/ p = i) by lia.
  destruct H as [Hlt | Heq].
  - apply Hscan_i; lia.
  - subst p; apply Hscan_j; lia.
Qed.
Lemma pair_sum_zero_ordered :
  forall l n i j,
    i <> j ->
    0 <= i < n ->
    0 <= j < n ->
    pair_sum_zero l i j ->
    exists p q,
      0 <= p < q /\ q < n /\ pair_sum_zero l p q.
Proof.
  intros l n i j Hij Hi Hj Hsum.
  unfold pair_sum_zero in *.
  destruct (Z_lt_ge_dec i j) as [Hij_lt | Hij_ge].
  - exists i, j. repeat split; lia.
  - exists j, i. repeat split; lia.
Qed.
Lemma problem_43_spec_false_of_scanned_i :
  forall input_l n limit,
    Zlength input_l = n ->
    n <= limit ->
    scanned_i input_l n limit ->
    problem_43_spec input_l false.
Proof.
  intros input_l n limit Hlen Hlimit Hscan.
  unfold problem_43_spec.
  split.
  - intros (i & j & Hij & Hi & Hj & Hsum).
    exfalso.
    rewrite Hlen in Hi, Hj.
    destruct (pair_sum_zero_ordered input_l n i j Hij Hi Hj)
      as (p & q & Hpq & Hq & Hpair).
    + unfold pair_sum_zero; exact Hsum.
    + unfold scanned_i in Hscan.
      specialize (Hscan p q Hpq Hq).
      exact ((Hscan ltac:(lia)) Hpair).
  - discriminate.
Qed.
Lemma problem_43_spec_true_of_pair :
  forall input_l n i j,
    Zlength input_l = n ->
    0 <= i < j ->
    j < n ->
    pair_sum_zero input_l i j ->
    problem_43_spec input_l true.
Proof.
  intros input_l n i j Hlen Hij Hjn Hpair.
  unfold problem_43_spec.
  split.
  - intro Hexists. reflexivity.
  - intro Heq.
    rewrite Hlen.
    exists i, j.
    unfold pair_sum_zero in Hpair.
    repeat split; try lia.
Qed.


Lemma proof_of_p043_pairs_sum_to_zero_safety_wit_4 : p043_pairs_sum_to_zero_safety_wit_4.
Proof.
  pre_process.
  assert (Hij : 0 <= i < j) by lia.
  assert (Hjn : j < l_size_pre) by lia.
  match goal with
  | H: pair_sum_int_range input_l l_size_pre |- _ =>
      pose proof (H i j Hij Hjn) as Hsum
  end.
  andp_cancel; lia.
Qed.

Lemma proof_of_p043_pairs_sum_to_zero_entail_wit_1 : p043_pairs_sum_to_zero_entail_wit_1.
Proof.
  pre_process.
  andp_cancel; auto; try lia; try apply scanned_i_init.
Qed.

Lemma proof_of_p043_pairs_sum_to_zero_entail_wit_2 : p043_pairs_sum_to_zero_entail_wit_2.
Proof.
  pre_process.
  andp_cancel; auto; try lia.
  apply scanned_j_init.
  assumption.
Qed.

Lemma proof_of_p043_pairs_sum_to_zero_entail_wit_3 : p043_pairs_sum_to_zero_entail_wit_3.
Proof.
  pre_process.
  assert (Hnext : scanned_i input_l l_size_pre (i + 1)).
  { apply scanned_i_step with (j := j); auto; lia. }
  andp_cancel; auto; try lia.
  sep_apply store_int_undef_store_int.
  andp_cancel; auto; try lia.
Qed.

Lemma proof_of_p043_pairs_sum_to_zero_entail_wit_4 : p043_pairs_sum_to_zero_entail_wit_4.
Proof.
  pre_process.
  assert (Hnext : scanned_j input_l l_size_pre i (j + 1)).
  { apply scanned_j_step.
    - assumption.
    - unfold pair_sum_zero.
      lia. }
  andp_cancel; auto; try lia.
Qed.

Lemma proof_of_p043_pairs_sum_to_zero_return_wit_1 : p043_pairs_sum_to_zero_return_wit_1.
Proof.
  pre_process.
  prop_apply (IntArray.full_Zlength l_pre). Intros.
  Left.
  andp_cancel; auto; try lia.
  apply problem_43_spec_false_of_scanned_i with (n := l_size_pre) (limit := i);
    auto; lia.
Qed.

Lemma proof_of_p043_pairs_sum_to_zero_return_wit_2 : p043_pairs_sum_to_zero_return_wit_2.
Proof.
  pre_process.
  prop_apply (IntArray.full_Zlength l_pre). Intros.
  Right.
  andp_cancel; auto; try lia.
  apply problem_43_spec_true_of_pair with (n := l_size_pre) (i := i) (j := j);
    auto; try lia.
Qed.

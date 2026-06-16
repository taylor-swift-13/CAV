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
From SimpleC.EE.CAV.verify_20260607_095223_p040_triples_sum_to_zero Require Import p040_triples_sum_to_zero_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p040_triples_sum_to_zero.
Local Open Scope sac.

Lemma scanned_i_zero :
  forall l n, scanned_i l n 0.
Proof.
  unfold scanned_i.
  intros.
  lia.
Qed.

Lemma scanned_i_to_scanned_j_start :
  forall l n i,
    scanned_i l n i ->
    scanned_j l n i (i + 1).
Proof.
  unfold scanned_i, scanned_j.
  intros l n i Hscan.
  split; [exact Hscan |].
  intros q r Hiq _ _ Hq.
  intro Htriple.
  lia.
Qed.

Lemma scanned_j_to_scanned_k_start :
  forall l n i j,
    scanned_j l n i j ->
    scanned_k l n i j (j + 1).
Proof.
  unfold scanned_j, scanned_k.
  intros l n i j Hscan.
  split; [exact Hscan |].
  intros r Hj Hrk.
  intro Htriple.
  lia.
Qed.

Lemma scanned_k_step :
  forall l n i j k,
    scanned_k l n i j k ->
    ~ triple_sum_zero l i j k ->
    scanned_k l n i j (k + 1).
Proof.
  unfold scanned_k.
  intros l n i j k [Hscan_j Hscan_k] Hneq.
  split; [exact Hscan_j |].
  intros r Hjr Hr.
  assert (r < k \/ r = k) by lia.
  destruct H as [Hlt | Heq].
  - apply Hscan_k; lia.
  - subst r; exact Hneq.
Qed.

Lemma scanned_k_finish :
  forall l n i j k,
    k = n ->
    scanned_k l n i j k ->
    scanned_j l n i (j + 1).
Proof.
  unfold scanned_j, scanned_k.
  intros l n i j k Hkn [[Hscan_i Hscan_j] Hscan_k].
  subst k.
  split; [exact Hscan_i |].
  intros q r Hiq Hqr Hrn Hq.
  assert (q < j \/ q = j) by lia.
  destruct H as [Hlt | Heq].
  - apply Hscan_j; lia.
  - subst q; apply Hscan_k; lia.
Qed.

Lemma scanned_j_finish :
  forall l n i j,
    j = n ->
    scanned_j l n i j ->
    scanned_i l n (i + 1).
Proof.
  unfold scanned_i, scanned_j.
  intros l n i j Hjn [Hscan_i Hscan_j].
  subst j.
  intros p q r Hp Hqr Hrn Hp_lt.
  assert (p < i \/ p = i) by lia.
  destruct H as [Hlt | Heq].
  - apply Hscan_i; lia.
  - subst p; apply Hscan_j; lia.
Qed.

Lemma triple_sum_zero_ordered :
  forall l n i j k,
    i <> j ->
    i <> k ->
    j <> k ->
    0 <= i < n ->
    0 <= j < n ->
    0 <= k < n ->
    triple_sum_zero l i j k ->
    exists p q r,
      0 <= p < q /\ q < r /\ r < n /\ triple_sum_zero l p q r.
Proof.
  intros l n i j k Hij Hik Hjk Hi Hj Hk Hsum.
  unfold triple_sum_zero in *.
  destruct (Z_lt_ge_dec i j) as [Hij_lt | Hij_ge].
  - destruct (Z_lt_ge_dec j k) as [Hjk_lt | Hjk_ge].
    + exists i, j, k. repeat split; lia.
    + assert (Hkj : k < j) by lia.
      destruct (Z_lt_ge_dec i k) as [Hik_lt | Hik_ge].
      * exists i, k, j. repeat split; lia.
      * assert (Hki : k < i) by lia.
        exists k, i, j. repeat split; lia.
  - assert (Hji : j < i) by lia.
    destruct (Z_lt_ge_dec i k) as [Hik_lt | Hik_ge].
    + destruct (Z_lt_ge_dec j k) as [Hjk_lt | Hjk_ge].
      * exists j, i, k. repeat split; lia.
      * assert (Hkj : k < j) by lia.
        exists k, j, i. repeat split; lia.
    + assert (Hki : k < i) by lia.
      destruct (Z_lt_ge_dec j k) as [Hjk_lt | Hjk_ge].
      * exists j, k, i. repeat split; lia.
      * assert (Hkj : k < j) by lia.
        exists k, j, i. repeat split; lia.
Qed.

Lemma problem_40_spec_false_of_scanned_i :
  forall input_l n,
    Zlength input_l = n ->
    scanned_i input_l n n ->
    problem_40_spec input_l false.
Proof.
  intros input_l n Hlen Hscan.
  unfold problem_40_spec.
  split.
  - intros (i & j & k & Hij & Hik & Hjk & Hi & Hj & Hk & Hsum).
    exfalso.
    rewrite Hlen in Hi, Hj, Hk.
    destruct (triple_sum_zero_ordered input_l n i j k Hij Hik Hjk Hi Hj Hk)
      as (p & q & r & Hpq & Hqr & Hr & Htriple).
    + unfold triple_sum_zero; exact Hsum.
    + unfold scanned_i in Hscan.
      specialize (Hscan p q r Hpq Hqr Hr).
      exact ((Hscan ltac:(lia)) Htriple).
  - discriminate.
Qed.

Lemma problem_40_spec_true_of_triple :
  forall input_l n i j k,
    Zlength input_l = n ->
    0 <= i < j ->
    j < k ->
    k < n ->
    triple_sum_zero input_l i j k ->
    problem_40_spec input_l true.
Proof.
  intros input_l n i j k Hlen Hij Hjk Hkn Htriple.
  unfold problem_40_spec.
  split.
  - intro Hexists. reflexivity.
  - intro Heq.
    rewrite Hlen.
    exists i, j, k.
    unfold triple_sum_zero in Htriple.
    repeat split; try lia.
Qed.

Lemma proof_of_p040_triples_sum_to_zero_safety_wit_6 : p040_triples_sum_to_zero_safety_wit_6.
Proof.
  pre_process.
  assert (Hrng :
    -2147483648 <= Znth i input_l 0 + Znth j input_l 0 + Znth k input_l 0 /\
    Znth i input_l 0 + Znth j input_l 0 + Znth k input_l 0 <= 2147483647).
  {
    unfold triple_sum_int_range in H3.
    specialize (H3 i j k ltac:(lia) ltac:(lia) ltac:(lia)).
    lia.
  }
  entailer!.
Qed.

Lemma proof_of_p040_triples_sum_to_zero_safety_wit_7 : p040_triples_sum_to_zero_safety_wit_7.
Proof.
  pre_process.
  assert (Hrng :
    -2147483648 <= Znth i input_l 0 + Znth j input_l 0 /\
    Znth i input_l 0 + Znth j input_l 0 <= 2147483647).
  {
    unfold triple_sum_int_range in H3.
    specialize (H3 i j k ltac:(lia) ltac:(lia) ltac:(lia)).
    lia.
  }
  entailer!.
Qed.

Lemma proof_of_p040_triples_sum_to_zero_entail_wit_1 : p040_triples_sum_to_zero_entail_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    apply scanned_i_zero.
Qed.

Lemma proof_of_p040_triples_sum_to_zero_entail_wit_2 : p040_triples_sum_to_zero_entail_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    apply scanned_i_to_scanned_j_start.
    assumption.
Qed.

Lemma proof_of_p040_triples_sum_to_zero_entail_wit_3 : p040_triples_sum_to_zero_entail_wit_3.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    apply scanned_j_to_scanned_k_start.
    assumption.
Qed.

Lemma proof_of_p040_triples_sum_to_zero_entail_wit_4 : p040_triples_sum_to_zero_entail_wit_4.
Proof.
  pre_process.
Qed.

Lemma proof_of_p040_triples_sum_to_zero_entail_wit_5 : p040_triples_sum_to_zero_entail_wit_5.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full l_pre l_size_pre input_l).
    sep_apply store_int_undef_store_int.
    cancel (((( &( "k" ) )) # Int  |->_)).
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    assert (k = l_size_pre) by lia.
    subst k.
    apply (scanned_k_finish input_l l_size_pre i j l_size_pre); [reflexivity | assumption].
Qed.

Lemma proof_of_p040_triples_sum_to_zero_entail_wit_6 : p040_triples_sum_to_zero_entail_wit_6.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    apply scanned_k_step.
    + assumption.
    + unfold not, triple_sum_zero.
      lia.
Qed.

Lemma proof_of_p040_triples_sum_to_zero_entail_wit_8 : p040_triples_sum_to_zero_entail_wit_8.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full l_pre l_size_pre input_l).
    sep_apply store_int_undef_store_int.
    cancel (((( &( "j" ) )) # Int  |->_)).
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    assert (j = l_size_pre) by lia.
    subst j.
    apply (scanned_j_finish input_l l_size_pre i l_size_pre); [reflexivity | assumption].
Qed.

Lemma proof_of_p040_triples_sum_to_zero_entail_wit_10 : p040_triples_sum_to_zero_entail_wit_10.
Proof.
  pre_process.
  assert (i = l_size_pre) by lia.
  subst i.
  entailer!.
Qed.

Lemma proof_of_p040_triples_sum_to_zero_return_wit_1 : p040_triples_sum_to_zero_return_wit_1.
Proof.
  pre_process.
  prop_apply IntArray.full_Zlength.
  Intros.
  entailer!.
  left.
  cbn.
  split.
  - reflexivity.
  - split.
    + apply (problem_40_spec_false_of_scanned_i input_l l_size_pre).
      * exact H4.
      * exact H3.
    + exact H5.
Qed.

Lemma proof_of_p040_triples_sum_to_zero_return_wit_2 : p040_triples_sum_to_zero_return_wit_2.
Proof.
  pre_process.
  prop_apply IntArray.full_Zlength.
  Intros.
  entailer!.
  right.
  cbn.
  split.
  - discriminate.
  - split.
    + apply (problem_40_spec_true_of_triple input_l l_size_pre i j k).
      * first [
          match goal with
          | Hlen : Zlength input_l = l_size_pre |- _ => exact Hlen
          end
        | match goal with
          | Hlen : l_size_pre = Zlength input_l |- _ => exact (eq_sym Hlen)
          end ].
      * lia.
      * lia.
      * lia.
      * match goal with
        | Htriple : triple_sum_zero input_l i j k |- _ => exact Htriple
        end.
    + match goal with
      | Hfull : IntArray.full l_pre l_size_pre input_l m |- _ => exact Hfull
      end.
Qed.

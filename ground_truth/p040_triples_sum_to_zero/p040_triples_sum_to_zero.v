(* spec/40 *)
(* triples_sum_to_zero takes a list of integers as an input.
it returns True if there are three distinct elements in the list that
sum to zero, and False otherwise.

>>> triples_sum_to_zero([1, 3, 5, 0])
False
>>> triples_sum_to_zero([1, 3, -2, 1])
True
>>> triples_sum_to_zero([1, 2, 3, 7])
False
>>> triples_sum_to_zero([2, 4, -5, 3, 9, 7])
True
>>> triples_sum_to_zero([1])
False *)

(*Spec(input : list int, output : bool) :=

​	∃i,j,k i<>k /\ i<>j /\ j<>k /\ input[i] + input[j] + input[k] = 0 → output = true /\
​	∀i,j,k i<>k /\ i<>j /\ j<>k /\ input[i] + input[j] + input[k] <> 0 → output = false *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From AUXLib Require Import ListLib.
Import ListNotations.
Open Scope Z_scope.
(* Pre: no additional constraints for `triples_sum_to_zero` by default *)
Definition problem_40_pre (input : list Z) : Prop := True.

Definition problem_40_spec (input : list Z) (output : bool) : Prop :=
  (*
    存在三个不同的索引 i, j, k，
    使得对应元素之和为 0。
    我们必须同时检查索引 i, j, k 在列表的有效范围内。
    nth 函数需要一个默认值 (这里是0)，如果索引越界，它会返回该默认值.
    但因为我们已经用 i < length input 等条件确保了索引有效，所以默认值不会被用到。
  *)
  (exists i j k : Z,
    (i <> j) /\ (i <> k) /\ (j <> k) /\
    0 <= i < Zlength input /\
    0 <= j < Zlength input /\
    0 <= k < Zlength input /\
    (Znth i input 0 + Znth j input 0 + Znth k input 0 = 0))
  <-> (output = true).

Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition triple_sum_int_range (l : list Z) (n : Z) : Prop :=
  forall i j k,
    0 <= i < j ->
    j < k ->
    k < n ->
    INT_MIN <= Znth i l 0 + Znth j l 0 <= INT_MAX /\
    INT_MIN <= Znth i l 0 + Znth j l 0 + Znth k l 0 <= INT_MAX.

Definition triple_sum_zero (l : list Z) (i j k : Z) : Prop :=
  Znth i l 0 + Znth j l 0 + Znth k l 0 = 0.

Definition scanned_i (l : list Z) (n i : Z) : Prop :=
  forall p q r,
    0 <= p < q ->
    q < r ->
    r < n ->
    p < i ->
    ~ triple_sum_zero l p q r.

Definition scanned_j (l : list Z) (n i j : Z) : Prop :=
  scanned_i l n i /\
  forall q r,
    i < q ->
    q < r ->
    r < n ->
    q < j ->
    ~ triple_sum_zero l i q r.

Definition scanned_k (l : list Z) (n i j k : Z) : Prop :=
  scanned_j l n i j /\
  forall r,
    j < r ->
    r < k ->
    ~ triple_sum_zero l i j r.

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
  intros q r Hiq _ _ Hq Htriple.
  lia.
Qed.

Lemma scanned_k_init :
  forall l n i j,
    scanned_j l n i j ->
    scanned_k l n i j (j + 1).
Proof.
  unfold scanned_k.
  intros l n i j Hscan.
  split; [exact Hscan |].
  intros r Hjr Hr Htriple.
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

Lemma scanned_j_step :
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

Lemma scanned_i_step :
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
      * exists k, i, j. repeat split; lia.
  - assert (Hji : j < i) by lia.
    destruct (Z_lt_ge_dec i k) as [Hik_lt | Hik_ge].
    + destruct (Z_lt_ge_dec j k) as [Hjk_lt | Hjk_ge].
      * exists j, i, k. repeat split; lia.
      * exists k, j, i. repeat split; lia.
    + destruct (Z_lt_ge_dec j k) as [Hjk_lt | Hjk_ge].
      * exists j, k, i. repeat split; lia.
      * exists k, j, i. repeat split; lia.
Qed.

Lemma problem_40_spec_false_of_scanned_i :
  forall input_l n limit,
    Zlength input_l = n ->
    n <= limit ->
    scanned_i input_l n limit ->
    problem_40_spec input_l false.
Proof.
  intros input_l n limit Hlen Hlimit Hscan.
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

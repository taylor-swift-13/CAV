(* spec/43 *)
(* pairs_sum_to_zero takes a list of integers as an input.
it returns True if there are two distinct elements in the list that
sum to zero, and False otherwise.
>>> pairs_sum_to_zero([1, 3, 5, 0])
False
>>> pairs_sum_to_zero([1, 3, -2, 1])
False
>>> pairs_sum_to_zero([1, 2, 3, 7])
False
>>> pairs_sum_to_zero([2, 4, -5, 3, 5, 7])
True
>>> pairs_sum_to_zero([1])
False *)

(* Spec(input : list int, output : bool) :=

​	∃i,j i<>j  /\ input[i] + input[j]  = 0 → output = true /\
​	∀i,j i<>j  /\ input[i] + input[j]  <> 0 → output = false *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From AUXLib Require Import ListLib.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `pairs_sum_to_zero` *)
Definition problem_43_pre (input : list Z) : Prop := True.

Definition problem_43_spec (input : list Z) (output : bool) : Prop :=
  (*
    存在两个不同的索引 i, j，
    使得对应元素之和为 0。
    我们必须同时检查索引 i, j 在列表的有效范围内。
    nth 函数需要一个默认值 (这里是0)，如果索引越界，它会返回该默认值。
    但因为我们已经用 i < length input 等条件确保了索引有效，所以默认值不会被用到。
  *)
  (exists i j : Z,
    (i <> j)  /\
    0 <= i < Zlength input /\
    0 <= j < Zlength input /\
    (Znth i input 0 + Znth j input 0 = 0))
  <-> (output = true).

Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition pair_sum_int_range (l : list Z) (n : Z) : Prop :=
  forall i j,
    0 <= i < j ->
    j < n ->
    INT_MIN <= Znth i l 0 + Znth j l 0 <= INT_MAX.

Definition pair_sum_zero (l : list Z) (i j : Z) : Prop :=
  Znth i l 0 + Znth j l 0 = 0.

Definition scanned_i (l : list Z) (n i : Z) : Prop :=
  forall p q,
    0 <= p < q ->
    q < n ->
    p < i ->
    ~ pair_sum_zero l p q.

Definition scanned_j (l : list Z) (n i j : Z) : Prop :=
  scanned_i l n i /\
  forall q,
    i < q ->
    q < n ->
    q < j ->
    ~ pair_sum_zero l i q.

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

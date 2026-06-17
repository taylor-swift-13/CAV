(* spec/90 *)
(* def next_smallest(lst):
"""
You are given a list of integers.
Write a function next_smallest() that returns the 2nd smallest element of the list.
Return None if there is no such element.

next_smallest([1, 2, 3, 4, 5]) == 2
next_smallest([5, 1, 4, 3, 2]) == 2
next_smallest([]) == None
next_smallest([1, 1]) == None
""" *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.


(*
  problem_90_spec l res

  一个描述 next_smallest 函数行为的规约。

  - l: 输入的整数列表 (list Z)
  - res: 函数的返回结果 (option Z)

  规约分为两种情况:
  1. 当函数返回 Some z (找到了第二小的值):
     - 必须存在一个最小值 s1。
     - z 必须在列表中，并且严格大于 s1。
     - z 必须是所有大于 s1 的元素中最小的那个。

  2. 当函数返回 None (没有找到第二小的值):
     - 这意味着列表中不存在两个或以上不同的元素。
*)

Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import naive_C_Rules.
Local Open Scope Z_scope.

Definition problem_90_pre (l : list Z) : Prop :=
  True.

Definition problem_90_spec (l : list Z) (res : Z) : Prop :=
  (res = -1 /\ (match None with
    | Some z => (* `Some` 情况：z 是第二小的值 *)
      exists s1,
        In s1 l /\                                (* 1. 存在一个元素 s1 在列表 l 中 *)
        (forall x, In x l -> s1 <= x) /\          (* 2. s1 是列表中的最小值 *)
        In z l /\                                 (* 3. z 也在列表 l 中 *)
        s1 < z /\                                 (* 4. z 严格大于最小值 s1 *)
        (forall y, In y l -> s1 < y -> z <= y)    (* 5. 对于任何大于 s1 的列表元素 y，z 都小于或等于 y *)

    | None => (* `None` 情况：列表中没有第二小的值 *)
      ~ (exists x y, In x l /\ In y l /\ x <> y)  (* 列表 l 中不存在两个不同的元素 *)
    end)) \/
    (match ((Some res)) with
    | Some z => (* `Some` 情况：z 是第二小的值 *)
      exists s1,
        In s1 l /\                                (* 1. 存在一个元素 s1 在列表 l 中 *)
        (forall x, In x l -> s1 <= x) /\          (* 2. s1 是列表中的最小值 *)
        In z l /\                                 (* 3. z 也在列表 l 中 *)
        s1 < z /\                                 (* 4. z 严格大于最小值 s1 *)
        (forall y, In y l -> s1 < y -> z <= y)    (* 5. 对于任何大于 s1 的列表元素 y，z 都小于或等于 y *)

    | None => (* `None` 情况：列表中没有第二小的值 *)
      ~ (exists x y, In x l /\ In y l /\ x <> y)  (* 列表 l 中不存在两个不同的元素 *)
    end).

Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
  if Z.eqb ascending 0 then True else Sorted Z.le l.

Definition no_distinct_prefix (i : Z) (l : list Z) : Prop :=
  forall k, 1 <= k < i -> Znth k l 0 = Znth (k - 1) l 0.

Definition next_smallest_sorted_bridge (input sorted_l : list Z) (size : Z) : Prop :=
  (forall i,
    1 <= i /\ i < size ->
    no_distinct_prefix i sorted_l ->
    Znth i sorted_l 0 <> Znth (i - 1) sorted_l 0 ->
    problem_90_spec input (Znth i sorted_l 0)) /\
  (no_distinct_prefix size sorted_l -> problem_90_spec input (-1)).

Lemma Znth_In_range : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma In_Znth_exists : forall (x : Z) l,
  In x l ->
  exists i, 0 <= i < Zlength l /\ Znth i l 0 = x.
Proof.
  intros x l Hin.
  apply In_nth_error in Hin.
  destruct Hin as [n Hn].
  exists (Z.of_nat n).
  split.
  - assert ((n < length l)%nat) as Hlt.
    { apply nth_error_Some. rewrite Hn. discriminate. }
    rewrite Zlength_correct.
    lia.
  - unfold Znth.
    rewrite Nat2Z.id.
    apply nth_error_nth with (d := 0) in Hn.
    exact Hn.
Qed.

Lemma Sorted_cons_all_le : forall x l y,
  Sorted Z.le (x :: l) ->
  In y (x :: l) ->
  x <= y.
Proof.
  intros x l.
  revert x.
  induction l; intros x y Hsorted Hin.
  - simpl in Hin.
    destruct Hin as [-> | []].
    lia.
  - simpl in Hin.
    destruct Hin as [-> | Hin].
    + lia.
    + pose proof (Sorted_inv Hsorted) as [Htail Hhd].
      assert (x <= a).
      {
        inversion Hhd; subst.
        assumption.
      }
      assert (a <= y).
      {
        apply IHl.
        - exact Htail.
        - simpl. exact Hin.
      }
      lia.
Qed.

Lemma nth_sorted_le_nat : forall l n m d,
  Sorted Z.le l ->
  (n <= m < length l)%nat ->
  nth n l d <= nth m l d.
Proof.
  induction l; intros n m d Hsorted Hrange.
  - simpl in Hrange. lia.
  - destruct n; destruct m; simpl.
    + lia.
    + apply (Sorted_cons_all_le a l (nth m l d)).
      * exact Hsorted.
      * right. apply nth_In. simpl in Hrange. lia.
    + lia.
    + pose proof (Sorted_inv Hsorted) as [Htail _].
      apply IHl.
      * exact Htail.
      * simpl in Hrange. lia.
Qed.

Lemma Sorted_Znth_le : forall l i j,
  Sorted Z.le l ->
  0 <= i <= j ->
  j < Zlength l ->
  Znth i l 0 <= Znth j l 0.
Proof.
  intros l i j Hsorted Hij Hj.
  unfold Znth.
  apply nth_sorted_le_nat.
  - exact Hsorted.
  - rewrite Zlength_correct in Hj.
    split.
    + apply Z2Nat.inj_le; lia.
    + apply Nat2Z.inj_lt.
      rewrite Z2Nat.id by lia.
      lia.
Qed.

Lemma no_distinct_prefix_eq0 : forall i l j,
  no_distinct_prefix i l ->
  0 <= j < i ->
  Znth j l 0 = Znth 0 l 0.
Proof.
  intros i l j Hpref Hj.
  assert (Hnat : forall n,
    Z.of_nat n < i ->
    Znth (Z.of_nat n) l 0 = Znth 0 l 0).
  {
    induction n; intros Hn.
    - reflexivity.
    - rewrite Nat2Z.inj_succ.
      rewrite Hpref by lia.
      replace (Z.succ (Z.of_nat n) - 1) with (Z.of_nat n) by lia.
      apply IHn.
      lia.
  }
  rewrite <- (Z2Nat.id j) by lia.
  apply Hnat.
  lia.
Qed.

Lemma no_distinct_prefix_1 : forall l,
  no_distinct_prefix 1 l.
Proof.
  unfold no_distinct_prefix.
  intros l k Hk.
  lia.
Qed.

Lemma next_smallest_sorted_bridge_of_sorted : forall input sorted_l size,
  size = Zlength sorted_l ->
  sorted_int_list_by 1 sorted_l ->
  Permutation input sorted_l ->
  next_smallest_sorted_bridge input sorted_l size.
Proof.
  intros input sorted_l size Hlen Hsorted_by Hperm.
  unfold sorted_int_list_by in Hsorted_by.
  simpl in Hsorted_by.
  unfold next_smallest_sorted_bridge.
  split.
  - intros i Hi Hpref Hdiff.
    right.
    exists (Znth 0 sorted_l 0).
    assert (Hsize : 1 < size) by lia.
    assert (Hsort_len : Zlength sorted_l = size) by lia.
    assert (Hin_min_sorted : In (Znth 0 sorted_l 0) sorted_l).
    { apply Znth_In_range. lia. }
    assert (Hin_z_sorted : In (Znth i sorted_l 0) sorted_l).
    { apply Znth_In_range. lia. }
    repeat split.
    + eapply Permutation_in.
      * apply Permutation_sym. exact Hperm.
      * exact Hin_min_sorted.
    + intros x Hx_input.
      assert (Hx_sorted : In x sorted_l).
      {
        eapply Permutation_in.
        - exact Hperm.
        - exact Hx_input.
      }
      destruct (In_Znth_exists x sorted_l Hx_sorted) as [j [Hj Hx]].
      rewrite <- Hx.
      eapply Sorted_Znth_le; eauto; lia.
    + eapply Permutation_in.
      * apply Permutation_sym. exact Hperm.
      * exact Hin_z_sorted.
    + assert (Znth (i - 1) sorted_l 0 = Znth 0 sorted_l 0).
      { eapply no_distinct_prefix_eq0; eauto; lia. }
      assert (Znth 0 sorted_l 0 <= Znth i sorted_l 0).
      { eapply Sorted_Znth_le; eauto; lia. }
      lia.
    + intros y Hy_input Hy_gt.
      assert (Hy_sorted : In y sorted_l).
      {
        eapply Permutation_in.
        - exact Hperm.
        - exact Hy_input.
      }
      destruct (In_Znth_exists y sorted_l Hy_sorted) as [j [Hj Hy]].
      rewrite <- Hy.
      destruct (Z_lt_ge_dec j i) as [Hji | Hji].
      * assert (Znth j sorted_l 0 = Znth 0 sorted_l 0).
        { eapply no_distinct_prefix_eq0; eauto; lia. }
        lia.
      * eapply Sorted_Znth_le; eauto; lia.
  - intros Hpref.
    left.
    split.
    + reflexivity.
    + intros [x [y [Hx [Hy Hneq]]]].
      assert (Hx_sorted : In x sorted_l).
      {
        eapply Permutation_in.
        - exact Hperm.
        - exact Hx.
      }
      assert (Hy_sorted : In y sorted_l).
      {
        eapply Permutation_in.
        - exact Hperm.
        - exact Hy.
      }
      destruct (In_Znth_exists x sorted_l Hx_sorted) as [ix [Hix Hxv]].
      destruct (In_Znth_exists y sorted_l Hy_sorted) as [iy [Hiy Hyv]].
      assert (Znth ix sorted_l 0 = Znth 0 sorted_l 0).
      { eapply no_distinct_prefix_eq0; eauto; lia. }
      assert (Znth iy sorted_l 0 = Znth 0 sorted_l 0).
      { eapply no_distinct_prefix_eq0; eauto; lia. }
      lia.
Qed.

Lemma no_distinct_prefix_step : forall i l,
  no_distinct_prefix i l ->
  1 <= i ->
  Znth i l 0 = Znth (i - 1) l 0 ->
  no_distinct_prefix (i + 1) l.
Proof.
  unfold no_distinct_prefix.
  intros i l Hpref Hi Heq k Hk.
  assert (k < i \/ k = i) by lia.
  destruct H as [Hlt | ->].
  - apply Hpref. lia.
  - exact Heq.
Qed.

Lemma problem_90_spec_short : forall l,
  Zlength l <= 1 ->
  problem_90_spec l (-1).
Proof.
  intros l Hlen.
  left.
  split.
  - reflexivity.
  - intros [x [y [Hx [Hy Hneq]]]].
    assert (length l <= 1)%nat.
    {
      rewrite Zlength_correct in Hlen.
      lia.
    }
    destruct l; simpl in *.
    + tauto.
    + destruct l; simpl in *.
      * destruct Hx as [-> | []].
        destruct Hy as [-> | []].
        contradiction.
      * lia.
Qed.

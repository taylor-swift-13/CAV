(* spec/123 *)
(* Given a positive integer n, return a sorted list that has the odd numbers in collatz sequence.

The Collatz conjecture is a conjecture in mathematics that concerns a sequence defined
as follows: start with any positive integer n. Then each term is obtained from the
previous term as follows: if the previous term is even, the next term is one half of
the previous term. If the previous term is odd, the next term is 3 times the previous
term plus 1. The conjecture is that no matter what value of n, the sequence will always reach 1.

Note:
1. Collatz(1) is [1].
2. returned list sorted in increasing order.

For example:
get_odd_collatz(5) returns [1, 5] # The collatz sequence for 5 is [5, 16, 8, 4, 2, 1], so the odd numbers are only 1, and 5. *)

(* 引用 Coq 标准库 *)
Require Import Coq.ZArith.ZArith.   (* 整数库 *)
Require Import Coq.Lists.List.      (* 列表库 *)
Require Import Coq.Sorting.Permutation. (* 列表置换关系 *)
Require Import Coq.Sorting.Sorted.      (* 列表排序谓词 *)

Import ListNotations.
Open Scope Z_scope.

(*
  辅助函数：带燃料的 Collatz 序列生成
*)
Fixpoint collatz_aux (n : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
    if Z.eqb n 1 then [1]
    else
      let next := if Z.even n then n / 2 else 3 * n + 1 in
      n :: collatz_aux next fuel'
  end.

(*
  [collatz_list n l] 定义：存在某个燃料使得生成的序列为 l，且序列以 1 结尾。
*)
Definition collatz_list (n : Z) (l : list Z) : Prop :=
  exists fuel, collatz_aux n fuel = l /\ last l 0 = 1.

(* n 为正整数 *)
(*
  [get_odd_collatz_spec n result] 定义了程序的规约。
  它描述了输入 [n] 和输出 [result] 之间必须满足的关系。
*)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import naive_C_Rules.
Local Open Scope Z_scope.

Inductive odd_collatz_prefix (original : Z) : Z -> list Z -> Prop :=
| odd_collatz_init :
    0 < original ->
    odd_collatz_prefix original original [1]
| odd_collatz_odd :
    forall n l,
      odd_collatz_prefix original n l ->
      n <> 1 ->
      n mod 2 = 1 ->
      odd_collatz_prefix original (3 * n + 1) (l ++ [n])
| odd_collatz_even :
    forall n l,
      odd_collatz_prefix original n l ->
      n <> 1 ->
      n mod 2 = 0 ->
      odd_collatz_prefix original (n / 2) l.

Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
  if Z.eqb ascending 0 then True else Sorted Z.le l.

Definition problem_123_spec (n : Z) (result : list Z) : Prop :=
  ((* 存在一个列表 c_seq ... *)
    exists (c_seq : list Z),
      (* ... c_seq 是 n 的 Collatz 序列 ... *)
      collatz_list n c_seq /\
      (* ... 并且，输出 result 是 c_seq 中所有奇数元素构成的列表的一个排列 ... *)
      Permutation result (filter (fun x => Z.odd x) c_seq) /\ (* <- 已修正 *)
      (* ... 并且，输出 result 必须是升序排列的。 *)
      Sorted Z.le result).

Definition collatz_step_safe (original current : Z) (output : list Z) : Prop :=
  odd_collatz_prefix original current output ->
  0 < current < INT_MAX /\
  0 < 3 * current + 1 < INT_MAX /\
  (current <> 1 -> Zlength output < 1024) /\
  (current mod 2 = 0 ->
     0 < current / 2 < INT_MAX).

Definition problem_123_pre (n : Z) : Prop :=
  0 < n < INT_MAX /\
  forall current output,
    collatz_step_safe n current output.

Inductive collatz_list_to (original : Z) : Z -> list Z -> Prop :=
| collatz_list_to_init :
    collatz_list_to original original []
| collatz_list_to_odd :
    forall n seq,
      collatz_list_to original n seq ->
      n <> 1 ->
      n mod 2 = 1 ->
      collatz_list_to original (3 * n + 1) (seq ++ [n])
| collatz_list_to_even :
    forall n seq,
      collatz_list_to original n seq ->
      n <> 1 ->
      n mod 2 = 0 ->
      collatz_list_to original (n / 2) (seq ++ [n]).

Lemma problem_123_pre_initial : forall n,
  problem_123_pre n ->
  0 < n < INT_MAX /\ odd_collatz_prefix n n [1].
Proof.
  intros n Hpre.
  destruct Hpre as [Hn _].
  split; [assumption | constructor; lia].
Qed.

Lemma collatz_step_safe_of_pre : forall original current output,
  problem_123_pre original ->
  odd_collatz_prefix original current output ->
  0 < current < INT_MAX /\
  0 < 3 * current + 1 < INT_MAX /\
  (current <> 1 -> Zlength output < 1024) /\
  (current mod 2 = 0 ->
     0 < current / 2 < INT_MAX).
Proof.
  intros original current output Hpre Hprefix.
  destruct Hpre as [_ Hsafe].
  unfold collatz_step_safe in Hsafe.
  apply Hsafe; assumption.
Qed.

Lemma Z_rem_2_eq_1_to_mod : forall n,
  0 < n ->
  n % 2 = 1 ->
  n mod 2 = 1.
Proof.
  intros n Hn Hrem.
  rewrite Z.rem_mod_nonneg in Hrem by lia.
  exact Hrem.
Qed.

Lemma Z_rem_2_neq_1_to_mod_0 : forall n,
  0 < n ->
  n % 2 <> 1 ->
  n mod 2 = 0.
Proof.
  intros n Hn Hrem.
  assert (Hmod_bound : 0 <= n mod 2 < 2) by (apply Z.mod_pos_bound; lia).
  rewrite Z.rem_mod_nonneg in Hrem by lia.
  lia.
Qed.

Lemma odd_collatz_odd_quot_step : forall original n output,
  odd_collatz_prefix original n output ->
  n <> 1 ->
  0 < n ->
  n % 2 = 1 ->
  odd_collatz_prefix original (n * 3 + 1) (output ++ [n]).
Proof.
  intros original n output Hprefix Hnot1 Hpos Hodd.
  replace (n * 3 + 1) with (3 * n + 1) by lia.
  apply odd_collatz_odd; try assumption.
  apply Z_rem_2_eq_1_to_mod; assumption.
Qed.

Lemma odd_collatz_even_quot_step : forall original n output,
  odd_collatz_prefix original n output ->
  n <> 1 ->
  0 < n ->
  n % 2 <> 1 ->
  odd_collatz_prefix original (n ÷ 2) output.
Proof.
  intros original n output Hprefix Hnot1 Hpos Heven.
  replace (n ÷ 2) with (n / 2).
  - apply odd_collatz_even; try assumption.
    apply Z_rem_2_neq_1_to_mod_0; assumption.
  - symmetry. apply Z.quot_div_nonneg; lia.
Qed.

Lemma Zmod_1_even_false_123 : forall n,
  n mod 2 = 1 ->
  Z.even n = false.
Proof.
  intros n Hmod.
  rewrite Zmod_odd in Hmod.
  destruct (Z.odd n) eqn:Hodd.
  - rewrite <- Z.negb_odd.
    rewrite Hodd.
    reflexivity.
  - discriminate.
Qed.

Lemma Zmod_0_even_true_123 : forall n,
  n mod 2 = 0 ->
  Z.even n = true.
Proof.
  intros n Hmod.
  rewrite Zeven_mod.
  apply Zeq_is_eq_bool.
  exact Hmod.
Qed.

Lemma collatz_aux_app_path_123 : forall original current seq,
  collatz_list_to original current seq ->
  forall fuel,
    collatz_aux original (length seq + fuel)%nat =
    seq ++ collatz_aux current fuel.
Proof.
  intros original current seq Hpath.
  induction Hpath; intros fuel.
  - reflexivity.
  - rewrite app_length.
    simpl.
    replace (length seq + 1 + fuel)%nat with (length seq + S fuel)%nat by lia.
    rewrite IHHpath.
    simpl.
    destruct (n =? 1) eqn:Hn1.
    { apply Z.eqb_eq in Hn1. contradiction. }
    rewrite Zmod_1_even_false_123 by assumption.
    replace (n * 3 + 1) with (3 * n + 1) by lia.
    rewrite <- app_assoc.
    reflexivity.
  - rewrite app_length.
    simpl.
    replace (length seq + 1 + fuel)%nat with (length seq + S fuel)%nat by lia.
    rewrite IHHpath.
    simpl.
    destruct (n =? 1) eqn:Hn1.
    { apply Z.eqb_eq in Hn1. contradiction. }
    rewrite Zmod_0_even_true_123 by assumption.
    rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma collatz_list_to_collatz_list_123 : forall original seq,
  collatz_list_to original 1 seq ->
  collatz_list original (seq ++ [1]).
Proof.
  intros original seq Hpath.
  unfold collatz_list.
  exists (length seq + 1)%nat.
  split.
  - rewrite collatz_aux_app_path_123 with (current := 1) (seq := seq) by assumption.
    simpl.
    reflexivity.
  - rewrite last_last.
    reflexivity.
Qed.

Lemma filter_odd_app_123 : forall l x,
  filter (fun x => Z.odd x) (l ++ [x]) =
  filter (fun x => Z.odd x) l ++
  if Z.odd x then [x] else [].
Proof.
  intros l x.
  rewrite filter_app.
  simpl.
  destruct (Z.odd x); reflexivity.
Qed.

Lemma odd_collatz_prefix_path_123 : forall original current raw_l,
  odd_collatz_prefix original current raw_l ->
  exists seq,
    collatz_list_to original current seq /\
    Permutation raw_l (1 :: filter (fun x => Z.odd x) seq).
Proof.
  intros original current raw_l Hprefix.
  induction Hprefix.
  - exists [].
    split.
    + constructor.
    + reflexivity.
  - destruct IHHprefix as [seq [Hpath Hperm]].
    exists (seq ++ [n]).
    split.
    + apply collatz_list_to_odd; assumption.
    + rewrite filter_odd_app_123.
      match goal with H : n mod 2 = 1 |- _ => rewrite Zmod_odd in H end.
      destruct (Z.odd n) eqn:Hodd.
      * simpl.
        eapply Permutation_trans.
        -- apply Permutation_app; [exact Hperm|reflexivity].
        -- reflexivity.
      * discriminate.
  - destruct IHHprefix as [seq [Hpath Hperm]].
    exists (seq ++ [n]).
    split.
    + apply collatz_list_to_even; assumption.
    + rewrite filter_odd_app_123.
      match goal with H : n mod 2 = 0 |- _ => rewrite Zmod_even in H end.
      destruct (Z.even n) eqn:Heven.
      * assert (Hodd : Z.odd n = false).
        {
          rewrite <- Z.negb_even.
          rewrite Heven.
          reflexivity.
        }
        rewrite Hodd.
        rewrite app_nil_r.
        exact Hperm.
      * discriminate.
Qed.

Lemma odd_collatz_prefix_original_spec_123 : forall original raw_l,
  odd_collatz_prefix original 1 raw_l ->
  exists c_seq,
    collatz_list original c_seq /\
    Permutation raw_l (filter (fun x => Z.odd x) c_seq).
Proof.
  intros original raw_l Hprefix.
  destruct (odd_collatz_prefix_path_123 _ _ _ Hprefix) as [seq [Hpath Hperm]].
  exists (seq ++ [1]).
  split.
  - apply collatz_list_to_collatz_list_123.
    exact Hpath.
  - rewrite filter_odd_app_123.
    simpl.
    eapply Permutation_trans.
    + exact Hperm.
    + rewrite <- (app_nil_r (1 :: filter (fun x : Z => Z.odd x) seq)).
      apply Permutation_middle.
Qed.

Lemma problem_123_spec_of_sorted : forall original raw_l sorted_l,
  odd_collatz_prefix original 1 raw_l ->
  sorted_int_list_by 1 sorted_l ->
  Permutation raw_l sorted_l ->
  problem_123_spec original sorted_l.
Proof.
  intros original raw_l sorted_l Hprefix Hsorted Hperm.
  unfold problem_123_spec.
  destruct (odd_collatz_prefix_original_spec_123 _ _ Hprefix)
    as [c_seq [Hcollatz Hraw_filter]].
  exists c_seq.
  repeat split.
  - exact Hcollatz.
  - eapply Permutation_trans.
    + apply Permutation_sym. exact Hperm.
    + exact Hraw_filter.
  - unfold sorted_int_list_by in Hsorted.
    simpl in Hsorted.
    exact Hsorted.
Qed.

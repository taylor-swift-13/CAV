(* spec/104 *)
(* Given a list of positive integers x. return a sorted list of all
elements that hasn't any even digit.

Note: Returned list should be sorted in increasing order.

For example:
>>> unique_digits([15, 33, 1422, 1])
[1, 15, 33]
>>> unique_digits([152, 323, 1422, 10])
[] *)

(* 导入所需的基础库 *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Bool.Bool.

Import ListNotations.

(* 辅助定义：判断单个数字是否为奇数 (与之前相同) *)
Definition is_odd_digit (d : nat) : Prop :=
  d = 1 \/ d = 3 \/ d = 5 \/ d = 7 \/ d = 9.

Fixpoint all_digits_odd_list (l : list nat) : Prop :=
  match l with
  | [] => True (* 空列表满足条件 *)
  | h :: t => is_odd_digit h /\ all_digits_odd_list t (* 头部是奇数且尾部也满足条件 *)
  end.

(*
  将 nat 转换为 list nat (使用结构递归)
*)

(*
  这是一个使用 "fuel" 技巧的辅助函数。
  - n: 我们要转换的数。
  - fuel: 一个计数器，确保递归会终止。递归调用在 fuel 的前驱 (fuel') 上进行。
*)
Fixpoint nat_to_digits_fueled (n fuel : nat) : list nat :=
  match fuel with
  | 0 => [] (* 燃料耗尽，停止 *)
  | S fuel' => (* 还有燃料，继续 *)
      (* 我们也需要检查 n 是否已经为0 *)
      if Nat.eqb n 0 then
        []
      else
        (n mod 10) :: nat_to_digits_fueled (n / 10) fuel'
  end.

(*
  主转换函数。
  它调用辅助函数，并提供足够的 "fuel"。
  一个安全的做法是提供 n 本身作为 fuel，因为一个数字的位数永远不会超过其本身的值。
*)
Definition nat_to_digits (n : nat) : list nat :=
  nat_to_digits_fueled n n.

Definition has_only_odd_digits (n : nat) : Prop :=
  all_digits_odd_list (nat_to_digits n).

(*
  第四部分: 实现函数
*)

(* 判断数字是否只有奇数字（bool版本） *)
Definition has_only_odd_digits_bool (n : nat) : bool :=
  let digits := nat_to_digits n in
  forallb (fun d => orb (Nat.eqb d 1) (orb (Nat.eqb d 3) (orb (Nat.eqb d 5) (orb (Nat.eqb d 7) (Nat.eqb d 9))))) digits.

(* 过滤函数 *)
Fixpoint filter_odd_digits_nat (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t =>
      if has_only_odd_digits_bool h then
        h :: filter_odd_digits_nat t
      else
        filter_odd_digits_nat t
  end.

(* 插入排序 *)
Fixpoint insert_sorted (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | h :: t =>
      if x <=? h then
        x :: l
      else
        h :: insert_sorted x t
  end.

Fixpoint sort_list (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert_sorted h (sort_list t)
  end.

Definition unique_digits_impl (x : list nat) : list nat :=
  sort_list (filter_odd_digits_nat x).

(* 列表元素均为正整数 *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import naive_C_Rules.
Local Open Scope Z_scope.

Definition problem_104_pre (l : list Z) : Prop :=
  Forall (fun n => 0 < n < INT_MAX) l.

Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
  if Z.eqb ascending 0 then True else
    forall original,
      Permutation original l ->
      map Z.to_nat l = sort_list (map Z.to_nat original).

Fixpoint zero_list_nat (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => 0 :: zero_list_nat n'
  end.

Definition zero_list (n : Z) : list Z :=
  zero_list_nat (Z.to_nat n).

Inductive odd_digit_scan_state (original : Z) : Z -> Z -> Prop :=
| odd_scan_init :
    0 < original ->
    odd_digit_scan_state original original 1
| odd_scan_even :
    forall num,
      odd_digit_scan_state original num 1 ->
      0 < num ->
      num mod 2 = 0 ->
      odd_digit_scan_state original (num / 10) 0
| odd_scan_odd :
    forall num,
      odd_digit_scan_state original num 1 ->
      0 < num ->
      num mod 2 <> 0 ->
      odd_digit_scan_state original (num / 10) 1.

Definition odd_digit_bool_104 (d : nat) : bool :=
  orb (Nat.eqb d 1)
      (orb (Nat.eqb d 3)
           (orb (Nat.eqb d 5)
                (orb (Nat.eqb d 7) (Nat.eqb d 9)))).

Definition only_odd_digits (n : Z) : Prop :=
  has_only_odd_digits_bool (Z.to_nat n) = true.

Definition has_even_digit (n : Z) : Prop :=
  has_only_odd_digits_bool (Z.to_nat n) = false.

Fixpoint filter_odd_digits (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t =>
      if has_only_odd_digits_bool (Z.to_nat h) then
        h :: filter_odd_digits t
      else
        filter_odd_digits t
  end.

Definition unique_digits_prefix (input : list Z) (i : Z) (output : list Z) : Prop :=
  0 <= i <= Zlength input /\
  output = filter_odd_digits (sublist 0 i input).

Definition problem_104_spec (input output : list Z) : Prop :=
  map Z.to_nat output = unique_digits_impl (map Z.to_nat input).

Lemma zero_list_nat_length : forall n,
  length (zero_list_nat n) = n.
Proof.
  induction n; simpl; lia.
Qed.

Lemma zero_list_Zlength : forall n,
  0 <= n ->
  Zlength (zero_list n) = n.
Proof.
  intros n Hn.
  unfold zero_list.
  rewrite Zlength_correct.
  rewrite zero_list_nat_length.
  lia.
Qed.

Lemma problem_104_pre_Znth : forall l i,
  problem_104_pre l ->
  0 <= i < Zlength l ->
  0 < Znth i l 0 < INT_MAX.
Proof.
  intros l i Hpre Hi.
  unfold problem_104_pre in Hpre.
  rewrite Forall_forall in Hpre.
  apply Hpre.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma odd_digit_scan_state_bounds : forall original num u,
  0 <= original ->
  odd_digit_scan_state original num u ->
  0 <= num <= original /\ (u = 0 \/ u = 1).
Proof.
  intros original num u Horig Hstate.
  induction Hstate.
  - split; lia.
  - destruct IHHstate as [Hbounds Hu].
    split.
    + assert (0 <= num / 10) by (apply Z.div_pos; lia).
      assert (num / 10 <= num).
      {
        apply Z.div_le_upper_bound; lia.
      }
      lia.
    + lia.
  - destruct IHHstate as [Hbounds Hu].
    split.
    + assert (0 <= num / 10) by (apply Z.div_pos; lia).
      assert (num / 10 <= num).
      {
        apply Z.div_le_upper_bound; lia.
      }
      lia.
    + lia.
Qed.

Lemma nat_to_digits_fueled_ge_104 : forall n fuel,
  (n <= fuel)%nat ->
  nat_to_digits_fueled n fuel = nat_to_digits n.
Proof.
  apply (well_founded_induction
           lt_wf
           (fun n => forall fuel, (n <= fuel)%nat ->
              nat_to_digits_fueled n fuel = nat_to_digits n)).
  intros n IH fuel Hle.
  destruct n.
  - destruct fuel; reflexivity.
  - destruct fuel.
    + lia.
    + unfold nat_to_digits at 1.
      simpl.
      assert (Hlt : (((S n) / 10) < S n)%nat).
      { apply Nat.div_lt; lia. }
      change (((S n mod 10)%nat :: nat_to_digits_fueled (S n / 10) fuel) =
              ((S n mod 10)%nat :: nat_to_digits_fueled (S n / 10) n)).
      rewrite (IH ((S n) / 10)%nat Hlt fuel) by lia.
      rewrite (IH ((S n) / 10)%nat Hlt n).
      * reflexivity.
      * destruct n.
        -- simpl. lia.
        -- change ((S (S n) / 10 <= S n)%nat).
           apply Nat.div_le_upper_bound; lia.
Qed.

Lemma nat_to_digits_step_104 : forall n,
  n <> O ->
  nat_to_digits n = (n mod 10)%nat :: nat_to_digits (n / 10).
Proof.
  intros n Hn.
  destruct n.
  - contradiction.
  - unfold nat_to_digits at 1.
    simpl.
    rewrite nat_to_digits_fueled_ge_104.
    + reflexivity.
    + destruct n.
      * simpl. lia.
      * change ((S (S n) / 10 <= S n)%nat).
        apply Nat.div_le_upper_bound; lia.
Qed.

Lemma has_only_odd_digits_bool_step_104 : forall n,
  0 < n ->
  has_only_odd_digits_bool (Z.to_nat n) =
    odd_digit_bool_104 (Z.to_nat (n mod 10)) &&
    has_only_odd_digits_bool (Z.to_nat (n / 10)).
Proof.
  intros n Hpos.
  unfold has_only_odd_digits_bool.
  rewrite nat_to_digits_step_104 by lia.
  change ((fun d : nat =>
       (d =? 1) || ((d =? 3) || ((d =? 5) || ((d =? 7) || (d =? 9)))))%nat
            (Z.to_nat n mod 10)%nat) with
    (odd_digit_bool_104 (Z.to_nat (n mod 10))).
  rewrite Z2Nat.inj_mod by lia.
  rewrite Z2Nat.inj_div by lia.
  reflexivity.
Qed.

Lemma odd_digit_bool_even_false_104 : forall d,
  (d < 10)%nat ->
  (d mod 2 = 0)%nat ->
  odd_digit_bool_104 d = false.
Proof.
  intros d Hd Hmod.
  unfold odd_digit_bool_104.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
Qed.

Lemma odd_digit_bool_odd_true_104 : forall d,
  (d < 10)%nat ->
  (d mod 2 <> 0)%nat ->
  odd_digit_bool_104 d = true.
Proof.
  intros d Hd Hmod.
  unfold odd_digit_bool_104.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
Qed.

Lemma mod10_mod2_104 : forall n,
  (n mod 10) mod 2 = n mod 2.
Proof.
  intros n.
  rewrite (Z.div_mod n 10) at 2 by lia.
  rewrite Z.add_mod by lia.
  rewrite Z.mul_mod by lia.
  change (10 mod 2) with 0.
  rewrite Z.mul_0_l.
  rewrite Z.add_0_l.
  rewrite Z.mod_mod by lia.
  reflexivity.
Qed.

Lemma has_only_odd_digits_bool_even_step_104 : forall n,
  0 < n ->
  n mod 2 = 0 ->
  has_only_odd_digits_bool (Z.to_nat n) = false.
Proof.
  intros n Hpos Heven.
  rewrite has_only_odd_digits_bool_step_104 by lia.
  rewrite odd_digit_bool_even_false_104.
  - reflexivity.
  - pose proof (Z.mod_pos_bound n 10 ltac:(lia)).
    lia.
  - apply Nat2Z.inj.
    rewrite Nat2Z.inj_mod by lia.
    rewrite Z2Nat.id by (pose proof (Z.mod_pos_bound n 10 ltac:(lia)); lia).
    rewrite mod10_mod2_104.
    exact Heven.
Qed.

Lemma has_only_odd_digits_bool_odd_step_104 : forall n,
  0 < n ->
  n mod 2 <> 0 ->
  has_only_odd_digits_bool (Z.to_nat n) =
  has_only_odd_digits_bool (Z.to_nat (n / 10)).
Proof.
  intros n Hpos Hodd.
  rewrite has_only_odd_digits_bool_step_104 by lia.
  rewrite odd_digit_bool_odd_true_104.
  - reflexivity.
  - pose proof (Z.mod_pos_bound n 10 ltac:(lia)).
    lia.
  - intro Hnat.
    apply (f_equal Z.of_nat) in Hnat.
    rewrite Nat2Z.inj_mod in Hnat by lia.
    rewrite Z2Nat.id in Hnat by (pose proof (Z.mod_pos_bound n 10 ltac:(lia)); lia).
    rewrite mod10_mod2_104 in Hnat.
    contradiction.
Qed.

Lemma odd_digit_scan_state_correct_104 : forall original num u,
  odd_digit_scan_state original num u ->
  (u = 1 ->
   has_only_odd_digits_bool (Z.to_nat original) =
   has_only_odd_digits_bool (Z.to_nat num)) /\
  (u = 0 ->
   has_only_odd_digits_bool (Z.to_nat original) = false).
Proof.
  intros original num u Hstate.
  induction Hstate.
  - split; intros; try reflexivity; lia.
  - destruct IHHstate as [Hkeep _].
    split.
    + intros Hfalse. lia.
    + intros _. rewrite Hkeep by reflexivity.
      apply has_only_odd_digits_bool_even_step_104; assumption.
  - destruct IHHstate as [Hkeep Hzero].
    split.
    + intros _. rewrite Hkeep by reflexivity.
      apply has_only_odd_digits_bool_odd_step_104; assumption.
    + intros Hfalse. lia.
Qed.

Lemma only_odd_digits_done : forall original num u,
  odd_digit_scan_state original num u ->
  (u = 0 \/ u = 1) ->
  num <= 0 ->
  u <> 0 ->
  only_odd_digits original.
Proof.
  intros original num u Hstate Hu01 Hnum Hu.
  unfold only_odd_digits.
  destruct (odd_digit_scan_state_correct_104 _ _ _ Hstate) as [Hone _].
  replace u with 1 in Hone by lia.
  rewrite Hone by reflexivity.
  replace (Z.to_nat num) with O by lia.
  reflexivity.
Qed.

Lemma has_even_digit_done : forall original num u,
  odd_digit_scan_state original num u ->
  u = 0 ->
  has_even_digit original.
Proof.
  intros original num u Hstate Hu.
  unfold has_even_digit.
  destruct (odd_digit_scan_state_correct_104 _ _ _ Hstate) as [_ Hzero].
  replace u with 0 in Hzero by lia.
  apply Hzero.
  reflexivity.
Qed.

Lemma odd_scan_even_quot : forall original num,
  odd_digit_scan_state original num 1 ->
  0 < num ->
  num % 2 = 0 ->
  odd_digit_scan_state original (num ÷ 10) 0.
Proof.
  intros original num Hstate Hpos Heven.
  replace (num ÷ 10) with (num / 10).
  - apply odd_scan_even with (num := num); try assumption.
    rewrite Z.rem_mod_nonneg in Heven by lia.
    exact Heven.
  - symmetry. apply Z.quot_div_nonneg; lia.
Qed.

Lemma odd_scan_odd_quot : forall original num,
  odd_digit_scan_state original num 1 ->
  0 < num ->
  num % 2 <> 0 ->
  odd_digit_scan_state original (num ÷ 10) 1.
Proof.
  intros original num Hstate Hpos Hodd.
  replace (num ÷ 10) with (num / 10).
  - apply odd_scan_odd with (num := num); try assumption.
    intro Hmod.
    apply Hodd.
    rewrite Z.rem_mod_nonneg by lia.
    exact Hmod.
  - symmetry. apply Z.quot_div_nonneg; lia.
Qed.

Lemma filter_odd_digits_snoc_true : forall l x,
  has_only_odd_digits_bool (Z.to_nat x) = true ->
  filter_odd_digits (l ++ [x]) = filter_odd_digits l ++ [x].
Proof.
  induction l; intros x Hx; simpl.
  - rewrite Hx. reflexivity.
  - destruct (has_only_odd_digits_bool (Z.to_nat a)); simpl; rewrite IHl; auto.
Qed.

Lemma filter_odd_digits_snoc_false : forall l x,
  has_only_odd_digits_bool (Z.to_nat x) = false ->
  filter_odd_digits (l ++ [x]) = filter_odd_digits l.
Proof.
  induction l; intros x Hx; simpl.
  - rewrite Hx. reflexivity.
  - destruct (has_only_odd_digits_bool (Z.to_nat a)); simpl; rewrite IHl; auto.
Qed.

Lemma map_filter_odd_digits : forall l,
  map Z.to_nat (filter_odd_digits l) =
  filter_odd_digits_nat (map Z.to_nat l).
Proof.
  induction l; simpl.
  - reflexivity.
  - destruct (has_only_odd_digits_bool (Z.to_nat a)); simpl; rewrite IHl; reflexivity.
Qed.

Lemma unique_digits_prefix_add_step : forall input i output,
  0 <= i < Zlength input ->
  unique_digits_prefix input i output ->
  only_odd_digits (Znth i input 0) ->
  unique_digits_prefix input (i + 1) (output ++ [Znth i input 0]).
Proof.
  intros input i output Hi Hprefix Hodd.
  unfold unique_digits_prefix in *.
  destruct Hprefix as [Hbounds Hout].
  split.
  - lia.
  - rewrite Hout.
    rewrite (sublist_split 0 (i + 1) i input)
      by (try rewrite <- Zlength_correct; lia).
    rewrite (sublist_single 0 i input) by lia.
    symmetry.
    apply filter_odd_digits_snoc_true.
    exact Hodd.
Qed.

Lemma unique_digits_prefix_skip_step : forall input i output,
  0 <= i < Zlength input ->
  unique_digits_prefix input i output ->
  has_even_digit (Znth i input 0) ->
  unique_digits_prefix input (i + 1) output.
Proof.
  intros input i output Hi Hprefix Heven.
  unfold unique_digits_prefix in *.
  destruct Hprefix as [Hbounds Hout].
  split.
  - lia.
  - rewrite Hout.
    rewrite (sublist_split 0 (i + 1) i input)
      by (try rewrite <- Zlength_correct; lia).
    rewrite (sublist_single 0 i input) by lia.
    symmetry.
    apply filter_odd_digits_snoc_false.
    exact Heven.
Qed.

Lemma problem_104_spec_of_sorted : forall input filtered output,
  unique_digits_prefix input (Zlength input) filtered ->
  sorted_int_list_by 1 output ->
  Permutation filtered output ->
  problem_104_spec input output.
Proof.
  intros input filtered output Hprefix Hsorted Hperm.
  unfold problem_104_spec, unique_digits_impl.
  unfold unique_digits_prefix in Hprefix.
  destruct Hprefix as [Hbounds Hfiltered].
  unfold sorted_int_list_by in Hsorted.
  change (Z.eqb 1 0) with false in Hsorted.
  rewrite (Hsorted filtered Hperm).
  rewrite Hfiltered.
  rewrite sublist_self by lia.
  rewrite map_filter_odd_digits.
  reflexivity.
Qed.

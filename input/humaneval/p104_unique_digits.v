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
  if Z.eqb ascending 0 then True else Sorted Z.le l.

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

Fixpoint has_only_odd_digits_z_fuel (fuel : nat) (n : Z) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
      if Z.leb n 0 then true
      else
        let d := Z.rem n 10 in
        odd_digit_bool_104 (Z.to_nat d) && has_only_odd_digits_z_fuel fuel' (Z.quot n 10)
  end.

Definition has_only_odd_digits_z (n : Z) : bool :=
  has_only_odd_digits_z_fuel (Z.to_nat n) n.

Definition only_odd_digits (n : Z) : Prop :=
  has_only_odd_digits_z n = true.

Definition has_even_digit (n : Z) : Prop :=
  has_only_odd_digits_z n = false.

Fixpoint filter_odd_digits (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t =>
      if has_only_odd_digits_z h then
        h :: filter_odd_digits t
      else
        filter_odd_digits t
  end.

Definition unique_digits_prefix (input : list Z) (i : Z) (output : list Z) : Prop :=
  0 <= i <= Zlength input /\
  output = filter_odd_digits (sublist 0 i input).

Definition problem_104_spec (input output : list Z) : Prop :=
  (forall x, In x output <-> In x input /\ only_odd_digits x) /\
  Sorted Z.le output /\
  NoDup output.

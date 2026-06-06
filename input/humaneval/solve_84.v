(* spec/84 *)
(* def solve(N):
"""Given a positive integer N, return the total sum of its digits in binary.

Example
For N = 1000, the sum of digits will be 1 the output should be "1".
For N = 150, the sum of digits will be 6 the output should be "110".
For N = 147, the sum of digits will be 12 the output should be "1100".

Variables:
@N integer
Constraints: 0 ≤ N ≤ 10000.
Output:
a string of binary number
""" *)
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

(*
  辅助函数 1.1: 一个带有“燃料”的、用于计算十进制各位数字之和的函数。
  递归在 fuel 参数上是结构性的，因此 Coq 可以接受这个定义。
*)
Fixpoint sum_decimal_digits_aux (fuel n : nat) : nat :=
  match fuel with
  | 0 => 0 (* 燃料耗尽，停止 *)
  | S f' => (* 还有燃料，继续计算 *)
    match n with
    | 0 => 0
    | _ => (n mod 10) + sum_decimal_digits_aux f' (n / 10)
    end
  end.

(*
  主函数 1: 计算自然数 N 的十进制各位数字之和。
  我们提供 N 本身作为初始燃料，这足以确保计算完成。
*)
Definition sum_decimal_digits (n : nat) : nat :=
  sum_decimal_digits_aux n n.

(*
  辅助函数 2.1: 一个带有“燃料”的、用于将正整数转为二进制字符串的函数。
  同样，递归在 fuel 上是结构性的。这个辅助函数假定 n > 0。
*)
Fixpoint nat_to_binary_string_pos_aux (fuel n : nat) : string :=
  match fuel with
  | 0 => "" (* 燃料耗尽 *)
  | S f' =>
      if Nat.eqb n 0 then ""
      else nat_to_binary_string_pos_aux f' (n / 2) ++ (if Nat.eqb (n mod 2) 0 then "0" else "1")
  end.

(*
  主函数 2: 将自然数 N 转换为其二进制表示的字符串。
  这里我们特殊处理 N=0 的情况，并为正数调用辅助函数。
*)
Definition nat_to_binary_string (n : nat) : string :=
  if Nat.eqb n 0 then "0"
  else nat_to_binary_string_pos_aux n n.

Definition solve_impl (N : nat) : string :=
  nat_to_binary_string (sum_decimal_digits N).



Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
Require Import string_bridge.
Require Import base_conversion_lib binary_digits_lib.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition problem_84_pre (N : Z) : Prop :=
  0 <= N <= 10 * 1000.

Definition problem_84_spec (N : Z) (output : list Z) : Prop :=
  string_of_list output = solve_impl (Z.to_nat N).

Definition decimal_sum_value (orig sum : Z) : Prop :=
  sum = Z.of_nat (sum_decimal_digits (Z.to_nat orig)).

Definition decimal_sum_state (orig x sum : Z) : Prop :=
  0 <= x /\
  0 <= sum /\
  sum + x <= orig /\
  exists fuel,
    (Z.to_nat x <= fuel)%nat /\
    sum + Z.of_nat (sum_decimal_digits_aux fuel (Z.to_nat x)) =
      Z.of_nat (sum_decimal_digits (Z.to_nat orig)).

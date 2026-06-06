(* spec/144 *)
(* def simplify(x, n):
Your task is to implement a function that will simplify the expression
x * n. The function returns True if x * n evaluates to a whole number and False
otherwise. Both x and n, are string representation of a fraction, and have the following format,
<numerator>/<denominator> where both numerator and denominator are positive whole numbers.

You can assume that x, and n are valid fractions, and do not have zero as denominator.

simplify("1/5", "5/1") = True
simplify("1/6", "2/1") = False
simplify("7/10", "10/2") = False *)
(* 导入所需的Coq库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* 将单个ASCII字符转换为数字 (0-9)，假设输入合法 *)
Definition char_to_digit (c : ascii) : nat :=
  let n := nat_of_ascii c in
  let zero := nat_of_ascii ("0"%char) in
  n - zero.

(* 辅助函数：将list ascii转换为自然数 *)
Fixpoint list_ascii_to_nat_aux (l : list ascii) (acc : nat) : nat :=
  match l with
  | [] => acc
  | c :: l' => list_ascii_to_nat_aux l' (acc * 10 + char_to_digit c)
  end.

(* 主函数：将list ascii转换为自然数 *)
Definition list_ascii_to_nat (l : list ascii) : nat :=
  list_ascii_to_nat_aux l 0.

Definition is_digit_ascii (c : ascii) : Prop :=
  nat_of_ascii ("0"%char) <= nat_of_ascii c <= nat_of_ascii ("9"%char).

Definition all_digits (l : list ascii) : Prop :=
  Forall is_digit_ascii l.

(*
 * 规约：Parse_Fraction
 * 描述：将一个由ASCII字符组成的列表解析为一个由分子和分母组成的自然数对。
 *
 * 参数：
 *   s: 代表分数字符串的 list ascii。
 *   num: 解析出的分子（自然数）。
 *   den: 解析出的分母（自然数）。
 *)
Definition Parse_Fraction (s : list ascii) (num den : nat) : Prop :=
  exists num_s den_s : list ascii,
    s = num_s ++ ["/"%char] ++ den_s /\
    num = list_ascii_to_nat num_s /\
    den = list_ascii_to_nat den_s.

(*
 * 规约：simplify_spec
 * 描述：这是`simplify`函数的顶层规约。它规定了输入与期望的布尔输出之间的关系。
 *       此版本完全使用 list ascii。
 *
 * 参数：
 *   x: 代表第一个分数的 list ascii。
 *   n: 代表第二个分数的 list ascii。
 *   output: 函数的期望布尔输出。
 *)
 (* 约束：x 与 n 均为有效分数串，且分子/分母为正整数 *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition problem_144_pre (x n : list Z) : Prop :=
  exists nx dx ny dy nx_s dx_s ny_s dy_s,
    list_ascii_of_string ((string_of_list x)) = nx_s ++ ["/"%char] ++ dx_s /\
    list_ascii_of_string ((string_of_list n)) = ny_s ++ ["/"%char] ++ dy_s /\
    all_digits nx_s /\ all_digits dx_s /\
    all_digits ny_s /\ all_digits dy_s /\
    nx = list_ascii_to_nat nx_s /\
    dx = list_ascii_to_nat dx_s /\
    ny = list_ascii_to_nat ny_s /\
    dy = list_ascii_to_nat dy_s /\
    Parse_Fraction (list_ascii_of_string ((string_of_list x))) nx dx /\
    Parse_Fraction (list_ascii_of_string ((string_of_list n))) ny dy /\
    (nx > 0 /\ dx > 0 /\ ny > 0 /\ dy > 0)%nat.

Definition problem_144_spec (x n : list Z) (output : Z) : Prop :=
  ((exists num_x den_x num_n den_n : nat,
      (* 1. 解析输入的 list ascii *)
      Parse_Fraction (list_ascii_of_string ((string_of_list x))) num_x den_x /\
      Parse_Fraction (list_ascii_of_string ((string_of_list n))) num_n den_n /\
  
      (* 2. 根据题目描述，分子和分母都是正整数（在nat中即 > 0） *)
      num_x > 0 /\ den_x > 0 /\
      num_n > 0 /\ den_n > 0 /\
  
      (* 3. 定义核心逻辑：乘积是否为整数 *)
      let product_num := num_x * num_n in
      let product_den := den_x * den_n in
      ((bool_of output)) = if (product_num mod product_den) =? 0
               then true
               else false)%nat).

Definition digit_char (c : Z) : Prop :=
  48 <= c <= 57.

Definition digit_value (c : Z) : Z :=
  c - 48.

Fixpoint parse_digits_z_aux (l : list Z) (acc : Z) : Z :=
  match l with
  | [] => acc
  | c :: rest => parse_digits_z_aux rest (acc * 10 + digit_value c)
  end.

Definition parse_digits (l : list Z) : Z :=
  parse_digits_z_aux l 0.

Definition fraction_parts (s : list Z) (slash num den : Z) : Prop :=
  0 < slash < Zlength s /\
  Znth slash s 0 = 47 /\
  (forall k, 0 <= k < slash -> digit_char (Znth k s 0)) /\
  (forall k, slash < k < Zlength s -> digit_char (Znth k s 0)) /\
  num = parse_digits (sublist 0 slash s) /\
  den = parse_digits (sublist (slash + 1) (Zlength s) s) /\
  (forall i, 0 <= i <= slash ->
     0 <= parse_digits (sublist 0 i s) <= num) /\
  (forall i, slash + 1 <= i <= Zlength s ->
     0 <= parse_digits (sublist (slash + 1) i s) <= den) /\
  0 < num /\ 0 < den.

Definition fraction_values_safe (a b c d : Z) : Prop :=
  1 <= a <= 46340 /\
  1 <= b <= 46340 /\
  1 <= c <= 46340 /\
  1 <= d <= 46340.

(* spec/79 *)
(* def decimal_to_binary(decimal):
"""You will be given a number in decimal form and your task is to convert it to
binary format. The function should return a string, with each character representing a binary
number. Each character in the string will be '0' or '1'.

There will be an extra couple of characters 'db' at the beginning and at the end of the string.
The extra characters are there to help with the format.

Examples:
decimal_to_binary(15) # returns "db1111db"
decimal_to_binary(32) # returns "db100000db"
""" *)
(* 导入Coq中处理字符串和列表所需的基础库 *)
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope string_scope.

(*
 * @brief 将布尔值列表转换为由 '0' 和 '1' 组成的字符串。
 *
 * 例如: binary_list_to_string [true; true; false; true] 会返回 "1101"
 *)
Fixpoint nat_to_binary_string_aux (n fuel : nat) : string :=
  match fuel with
  | O => ""
  | S fuel' =>
      match n with
      | O => "0"
      | 1 => "1"
      | _ =>
          if Nat.even n then
            nat_to_binary_string_aux (n / 2) fuel' ++ "0"
          else
            nat_to_binary_string_aux ((n - 1) / 2) fuel' ++ "1"
      end
  end.

Definition nat_to_binary_string (n : nat) : string :=
  match n with
  | O => "0"
  | _ => nat_to_binary_string_aux n n
  end.

Definition decimal_to_binary_impl (decimal : nat) : string :=
  "db" ++ nat_to_binary_string decimal ++ "db".
  

(* spec/103 *)
(* You are given two positive integers n and m, and your task is to compute the
average of the integers from n through m (including n and m).
Round the answer to the nearest integer and convert that to binary.
If n is greater than m, return -1.
Example:
rounded_avg(1, 5) => "11"
rounded_avg(7, 5) => "-1"
rounded_avg(10, 20) => "1111"
rounded_avg(20, 33) => "11010" *)

(* 引入所需的库 *)
Require Import ZArith.
Require Import String.
Require Import PArith. (* 用于 positive 类型 *)
Open Scope Z_scope.

(*
  一个作用于 positive 类型的递归辅助函数，用于生成二进制字符串。
  这是在 Coq 中进行此类转换的标准方法。
*)
Fixpoint to_binary_p (p : positive) : string :=
  match p with
  | xH    => "1" (* Base case for p = 1 *)
  | xO p' => to_binary_p p' ++ "0" (* Case for p = 2 * p' *)
  | xI p' => to_binary_p p' ++ "1" (* Case for p = 2 * p' + 1 *)
  end.

(*
  主转换函数，用于将 Z 类型（整数）转换为不带前缀的二进制字符串。
  它处理了 0 的情况，并使用 to_binary_p 处理正数。
*)
Definition to_binary (n : Z) : string :=
  match n with
  | Z0 => "0"
  | Zpos p => to_binary_p p
  | Zneg _ => "-1"
  end.

Definition rounded_avg_impl (n m : Z) : string :=
  if Z.gtb n m then
    "-1"
  else
    to_binary ((n + m) / 2).

(* n 与 m 为正整数 *)
Definition problem_103_pre (n m : Z) : Prop := n > 0 /\ m > 0.

Definition problem_103_spec (n m : Z) (output : string) : Prop :=
  output = rounded_avg_impl n m.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
Require Import string_bridge.
Require Import base_conversion_lib binary_digits_lib.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition problem_79_pre (decimal : Z) : Prop :=
  True.

Definition decorated_binary_digits (decimal : Z) : list Z :=
  [100; 98] ++ binary_digits decimal ++ [100; 98].

Definition problem_79_spec (decimal : Z) (output : list Z) : Prop :=
  output = decorated_binary_digits decimal.

Definition decimal_binary_full_state
  (orig x digits : Z) (out_l : list Z) : Prop :=
  exists payload,
    binary_fill_full_state orig x digits payload /\
    out_l = [100; 98] ++ payload ++ [100; 98].

Local Open Scope nat_scope.

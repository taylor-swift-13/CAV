(* spec/156 *)
(* def int_to_mini_roman(number):
"""
Given a positive integer, obtain its roman numeral equivalent as a string,
and return it in lowercase.
Restrictions: 1 <= num <= 1000

Examples:
>>> int_to_mini_roman(19) == 'xix'
>>> int_to_mini_roman(152) == 'clii'
>>> int_to_mini_roman(426) == 'cdxxvi'
""" *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith. (* <-- 添加这一行来导入算术库 *)
Import ListNotations.

(*
  一个辅助规约，用于定义单个数字（0-9）到其小写罗马数字字符（作为 list ascii）的映射。
  - roman_char:  i, v, x
*)
Definition roman_digit_spec (one ten five : ascii) (digit : nat) (res : list ascii) : Prop :=
  (digit = 0 /\ res = []) \/
  (digit = 1 /\ res = [one]) \/
  (digit = 2 /\ res = [one; one]) \/
  (digit = 3 /\ res = [one; one; one]) \/
  (digit = 4 /\ res = [one; five]) \/
  (digit = 5 /\ res = [five]) \/
  (digit = 6 /\ res = [five; one]) \/
  (digit = 7 /\ res = [five; one; one]) \/
  (digit = 8 /\ res = [five; one; one; one]) \/
  (digit = 9 /\ res = [one; ten]).

(* 输入限制：1 <= number <= 1000 *)

(*
  int_to_mini_roman 程序的程序规约
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
Require Import string_bridge.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition problem_156_pre (number : Z) : Prop :=
  1 <= number <= 1000.

Definition roman_digit_list (one ten five digit : Z) : list Z :=
  match digit with
  | 0 => []
  | 1 => [one]
  | 2 => [one; one]
  | 3 => [one; one; one]
  | 4 => [one; five]
  | 5 => [five]
  | 6 => [five; one]
  | 7 => [five; one; one]
  | 8 => [five; one; one; one]
  | 9 => [one; ten]
  | _ => []
  end.

Definition roman_digit
  (one ten five digit : Z) (chunk : list Z) : Prop :=
  chunk = roman_digit_list one ten five digit.

Definition roman_thousand_list (number : Z) : list Z :=
  if Z.eqb number 1000 then [109] else [].

Definition roman_thousand (number : Z) (out_l : list Z) : Prop :=
  out_l = roman_thousand_list number.

Definition roman_prefix1_list (number : Z) : list Z :=
  roman_thousand_list number ++
  roman_digit_list 99 109 100 ((number / 100) mod 10).

Definition roman_prefix1 (number : Z) (out_l : list Z) : Prop :=
  out_l = roman_prefix1_list number.

Definition roman_prefix2_list (number : Z) : list Z :=
  roman_prefix1_list number ++
  roman_digit_list 120 99 108 ((number / 10) mod 10).

Definition roman_prefix2 (number : Z) (out_l : list Z) : Prop :=
  out_l = roman_prefix2_list number.

Definition roman_output_list (number : Z) : list Z :=
  roman_prefix2_list number ++
  roman_digit_list 105 120 118 (number mod 10).

Definition roman_output (number : Z) (out_l : list Z) : Prop :=
  out_l = roman_output_list number.

Definition problem_156_spec (number : Z) (output : list Z) : Prop :=
  1 <= number <= 1000 /\
  output = roman_output_list number.

(* Helper lemmas migrated from the old proof, with names aligned to the input spec. *)

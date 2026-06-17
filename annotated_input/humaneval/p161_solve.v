(* spec/161 *)
(* def solve(s):
"""You are given a string s.
if s[i] is a letter, reverse its case from lower to upper or vise versa,
otherwise keep it as it is.
If the string contains no letters, reverse the string.
The function should return the resulted string.
Examples
solve("1234") = "4321"
solve("ab") = "AB"
solve("#a@C") = "#A@c"
""" *)
(* 引入所需的库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith. (* 需要引入这个库来进行自然数运算 *)
Require Import Coq.Strings.String.
Import ListNotations.

(*
  辅助定义
*)

(* 判断一个 ascii 字符是否为小写字母 *)
Definition is_lower_alpha (a : ascii) : bool :=
  (("a"%char <=? a)%char && (a <=? "z"%char)%char).

(* 判断一个 ascii 字符是否为大写字母 *)
Definition is_upper_alpha (a : ascii) : bool :=
  (("A"%char <=? a)%char && (a <=? "Z"%char)%char).

(* 判断一个 ascii 字符是否为字母 *)
Definition is_letter_dec (a : ascii) : bool :=
  is_lower_alpha a || is_upper_alpha a.

(* 自定义的大小写转换函数 *)

(* 将小写字母转为大写。如果不是小写字母，则保持不变。
   原理：nat_of_ascii a - 32 *)
Definition my_uppercase (a : ascii) : ascii :=
  if is_lower_alpha a
  then ascii_of_nat (nat_of_ascii a - 32)
  else a.

(* 将大写字母转为小写。如果不是大写字母，则保持不变。
   原理：nat_of_ascii a + 32 *)
Definition my_lowercase (a : ascii) : ascii :=
  if is_upper_alpha a
  then ascii_of_nat (nat_of_ascii a + 32)
  else a.

(* 定义一个函数 change_case 来转换字母的大小写。
   现在它使用我们自定义的转换函数。 *)
Definition change_case (a : ascii) : ascii :=
  if is_lower_alpha a then
    my_uppercase a
  else if is_upper_alpha a then
    my_lowercase a
  else
    a.

(* 定义一个递归函数 contains_letter_dec 来判断一个列表 (字符串) 是否包含任何字母。*)
Fixpoint contains_letter_dec (s : list ascii) : bool :=
  match s with
  | [] => false
  | h :: t => is_letter_dec h || contains_letter_dec t
  end.

Definition solve_impl (s : string) : string :=
  let l := list_ascii_of_string s in
  if contains_letter_dec l
  then string_of_list_ascii (map change_case l)
  else string_of_list_ascii (rev l).

(* 任意字符串输入 *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.BinNat.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition ascii_range (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> 0 <= Znth i s 0 <= 127.

Definition is_lower_zb (c : Z) : bool :=
  (Z.leb 97 c) && (Z.leb c 122).

Definition is_upper_zb (c : Z) : bool :=
  (Z.leb 65 c) && (Z.leb c 90).

Definition is_letter_zb (c : Z) : bool :=
  is_lower_zb c || is_upper_zb c.

Definition flip_char (c : Z) : Z :=
  if is_lower_zb c then c - 32
  else if is_upper_zb c then c + 32
  else c.

Fixpoint contains_letter_list (l : list Z) : bool :=
  match l with
  | [] => false
  | c :: rest => is_letter_zb c || contains_letter_list rest
  end.

Definition contains_letter_prefix (i : Z) (l : list Z) : Z :=
  if contains_letter_list (firstn (Z.to_nat i) l) then 1 else 0.

Definition contains_letter (l : list Z) : Z :=
  if contains_letter_list l then 1 else 0.

Definition problem_161_pre (s : list Z) : Prop :=
  True.

Definition problem_161_spec (input output : list Z) : Prop :=
  string_of_list output = solve_impl (string_of_list input).

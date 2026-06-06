(* spec/132 *)
(* def is_nested(string):
'''
Create a function that takes a string as input which contains only square brackets.
The function should return True if and only if there is a valid subsequence of brackets
where at least one bracket in the subsequence is nested.

is_nested('[[]]') ➞ True
is_nested('[]]]]]]][[[[[]') ➞ False
is_nested('[][]') ➞ False
is_nested('[]') ➞ False
is_nested('[[][]]') ➞ True
is_nested('[[]][[') ➞ True
''' *)
(* 引入 Coq 标准库中的字符串、列表和 Ascii 字符集 *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

(* 定义开方括号和闭方括号的 Ascii 字符表示 *)
Definition open_bracket : ascii := "["%char.
Definition close_bracket : ascii := "]"%char.

Fixpoint contains_subseq (s : list ascii) (target : list ascii) : bool :=
  match target with
  | [] => true
  | t :: ts =>
      match s with
      | [] => false
      | c :: cs =>
          if Ascii.ascii_dec c t then
            contains_subseq cs ts
          else
            contains_subseq cs target
      end
  end.

Definition is_nested (s : string) : bool :=
  contains_subseq (list_ascii_of_string s) [open_bracket; open_bracket; close_bracket; close_bracket].

(* 仅允许 '[' 或 ']' 字符 *)

(*
  程序规约：is_nested_spec s_in output
  它将输入字符串 s_in 与布尔输出 output 关联起来。
  
  规约内容：
  输出为 `true` 当且仅当输入字符串包含 "[[]]" 作为子序列。
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition bracket_char (c : Z) : Prop :=
  c = 91 \/ c = 93.

Definition problem_132_pre (s : list Z) : Prop :=
  Forall (fun c => c = "["%char \/ c = "]"%char) (list_ascii_of_string ((string_of_list s))).

Definition problem_132_spec (s : list Z) (output : Z) : Prop :=
  bool_of output = is_nested (string_of_list s).

Definition subseq_step (state c : Z) : Z :=
  if Z.eqb state 0 then
    if Z.eqb c 91 then 1 else 0
  else if Z.eqb state 1 then
    if Z.eqb c 91 then 2 else 1
  else if Z.eqb state 2 then
    if Z.eqb c 93 then 3 else 2
  else if Z.eqb state 3 then
    if Z.eqb c 93 then 4 else 3
  else 4.

Fixpoint subseq_state_list (state : Z) (s : list Z) : Z :=
  match s with
  | [] => state
  | c :: rest => subseq_state_list (subseq_step state c) rest
  end.

Definition subseq_state_prefix (i : Z) (s : list Z) : Z :=
  subseq_state_list 0 (firstn (Z.to_nat i) s).

Definition subseq_step_ascii (state : Z) (c : ascii) : Z :=
  if Z.eqb state 0 then
    if Ascii.ascii_dec c "["%char then 1 else 0
  else if Z.eqb state 1 then
    if Ascii.ascii_dec c "["%char then 2 else 1
  else if Z.eqb state 2 then
    if Ascii.ascii_dec c "]"%char then 3 else 2
  else if Z.eqb state 3 then
    if Ascii.ascii_dec c "]"%char then 4 else 3
  else 4.

Fixpoint subseq_state_list_ascii (state : Z) (s : list ascii) : Z :=
  match s with
  | [] => state
  | c :: rest => subseq_state_list_ascii (subseq_step_ascii state c) rest
  end.

Definition target_of_state (state : Z) : list ascii :=
  if Z.eqb state 0 then ["["%char; "["%char; "]"%char; "]"%char]
  else if Z.eqb state 1 then ["["%char; "]"%char; "]"%char]
  else if Z.eqb state 2 then ["]"%char; "]"%char]
  else if Z.eqb state 3 then ["]"%char]
  else [].

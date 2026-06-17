(* spec/140 *)
(* def fix_spaces(text):
Given a string text, replace all spaces in it with underscores,
and if a string has more than 2 consecutive spaces,
then replace all consecutive spaces with -

fix_spaces("Example") == "Example"
fix_spaces("Example 1") == "Example_1"
fix_spaces(" Example 2") == "_Example_2"
fix_spaces(" Example 3") == "_Example-3" *)
(* 导入列表和ASCII字符所需的基础库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

(* 为清晰起见，定义字符常量 *)
Definition space : ascii := " ".
Definition underscore : ascii := "_".
Definition dash : ascii := "-".

Definition flush_spaces_nat (n : nat) : list ascii :=
  match n with
  | 0 => []
  | 1 => [underscore]
  | 2 => [underscore; underscore]
  | _ => [dash]
  end.

(*
  核心函数: `fix_spaces_func input`
  pending 记录当前尚未输出的连续空格段长度。
  遇到非空格时先输出 pending 空格段，再输出当前字符。
*)
Fixpoint fix_spaces_scan (l : list ascii) (pending : nat) : list ascii :=
  match l with
  | [] => flush_spaces_nat pending
  | c :: tl =>
      if Ascii.ascii_dec c space then
        fix_spaces_scan tl (S pending)
      else
        flush_spaces_nat pending ++ c :: fix_spaces_scan tl 0
  end.

Definition fix_spaces (s : string) : string :=
  let l := list_ascii_of_string s in
  string_of_list_ascii (fix_spaces_scan l 0).

(* 输入文本任意 *)
(*
  程序规约 (Spec)
  它断言输出列表等于 `fix_spaces` 函数对输入列表的应用结果。
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition problem_140_pre (s : list Z) : Prop :=
  True.

Definition ascii_range (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> 0 <= Znth i s 0 <= 127.

Definition flush_spaces (n : Z) : list Z :=
  if Z.eqb n 0 then []
  else if Z.eqb n 1 then [95]
  else if Z.eqb n 2 then [95; 95]
  else [45].

Definition flush_spaces_len (n : Z) : Z :=
  if Z.eqb n 0 then 0
  else if Z.eqb n 1 then 1
  else if Z.eqb n 2 then 2
  else 1.

Definition scan_step (st : list Z * Z) (c : Z) : list Z * Z :=
  let '(out, pending) := st in
  if Z.eqb c 32 then
    (out, pending + 1)
  else
    (out ++ flush_spaces pending ++ [c], 0).

Definition fix_spaces_state (i : Z) (s : list Z) : list Z * Z :=
  fold_left scan_step (firstn (Z.to_nat i) s) ([], 0).

Definition fix_spaces_prefix (i : Z) (s : list Z) : list Z :=
  fst (fix_spaces_state i s).

Definition fix_spaces_pending (i : Z) (s : list Z) : Z :=
  snd (fix_spaces_state i s).

Definition fix_spaces_output (s : list Z) : list Z :=
  fix_spaces_prefix (Zlength s) s ++
  flush_spaces (fix_spaces_pending (Zlength s) s).

Definition problem_140_spec (input output : list Z) : Prop :=
  string_of_list output = fix_spaces (string_of_list input).

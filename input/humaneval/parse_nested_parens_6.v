(* spec/6 *)
(* Input to this function is a string represented multiple groups for nested parentheses separated by spaces.
For each of the group, output the deepest level of nesting of parentheses.
E.g. (()()) has maximum two levels of nesting while ((())) has three.

>>> parse_nested_parens('(()()) ((())) () ((())()())')
[2, 3, 1, 3] *)

Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import PeanoNat.
Import ListNotations.
Open Scope string_scope.

(* 定义 '(' 和 ')' 和 ' ' 的 ASCII 表示 *)
Definition lparen : ascii := "(".
Definition rparen : ascii := ")".
Definition space : ascii := " ".

(*
  规约 1: MaxDepth(g)
  计算单个括号组的最大嵌套深度。
*)
Fixpoint max_depth_aux (g : string) (current_depth max_seen : nat) : nat :=
  match g with
  | EmptyString => max_seen
  | String h t =>
    if ascii_dec h lparen then
      let new_depth := S current_depth in
      max_depth_aux t new_depth (Nat.max max_seen new_depth)
    else if ascii_dec h rparen then
      max_depth_aux t (Nat.pred current_depth) max_seen
    else
      max_depth_aux t current_depth max_seen (* 忽略其他字符 *)
  end.

Definition MaxDepth (g : string) : nat :=
  max_depth_aux g 0 0.

(*
  规约 2: SplitOnSpaces(S)
  将一个字符列表按空格分割成一个列表的列表。
*)
Fixpoint SplitOnSpaces_aux (current_group : list ascii) (S : string) : list string :=
  match S with
  | EmptyString =>
    match current_group with
    | [] => []
    | _ => [string_of_list_ascii (List.rev current_group)]
    end
  | String h t =>
    if ascii_dec h space then
      match current_group with
      | [] => SplitOnSpaces_aux [] t (* 多个或前导空格 *)
      | _ => (string_of_list_ascii (List.rev current_group)) :: SplitOnSpaces_aux [] t
      end
    else
      SplitOnSpaces_aux (h :: current_group) t
  end.

Definition SplitOnSpaces (S : string) : list string :=
  SplitOnSpaces_aux [] S.

(*
  最终的程序规约: parse_nested_parens_spec(input, output)
  输入是 string, 输出是 list nat。
*)

(*
  辅助断言: 检查一个字符是否为括号或空格
  直接使用等式，其类型为 Prop
*)
Definition is_paren_or_space (c : ascii) : Prop :=
  c = lparen \/ c = rparen \/ c = space.

Fixpoint IsBalanced_aux (l : string) (count : nat) : Prop :=
  match l with
  | EmptyString => count = 0
  | String h t =>
    if ascii_dec h lparen then
      IsBalanced_aux t (S count)
    else if ascii_dec h rparen then
      match count with
      | 0 => False (* 右括号比左括号多，不平衡 *)
      | S n' => IsBalanced_aux t n'
      end
    else
      IsBalanced_aux t count (* 忽略其他字符 *)
  end.

Definition IsBalanced (l : string) : Prop :=
  IsBalanced_aux l 0.
  

Fixpoint parse_nested_parens_scan_aux
  (input : string) (out : list nat) (in_group : bool)
  (current_depth max_seen : nat) : list nat :=
  match input with
  | EmptyString =>
    if in_group then out ++ [max_seen] else out
  | String h t =>
    if ascii_dec h space then
      if in_group then
        parse_nested_parens_scan_aux t (out ++ [max_seen]) false 0 0
      else
        parse_nested_parens_scan_aux t out false current_depth max_seen
    else if ascii_dec h lparen then
      let new_depth := S current_depth in
      parse_nested_parens_scan_aux t out true new_depth (Nat.max max_seen new_depth)
    else if ascii_dec h rparen then
      parse_nested_parens_scan_aux t out true (Nat.pred current_depth) max_seen
    else
      parse_nested_parens_scan_aux t out in_group current_depth max_seen
  end.

Definition parse_nested_parens_impl (input : string) : list nat :=
  parse_nested_parens_scan_aux input [] false 0 0.

(*
  辅助函数: 检查字符串中的所有字符是否满足属性 P
*)
Fixpoint ForallChars (P : ascii -> Prop) (s : string) : Prop :=
  match s with
  | EmptyString => True
  | String h t => P h /\ ForallChars P t
  end.

(*
  前提条件: separate_paren_groups_pre
  1. 输入列表中的所有字符都必须是括号或空格。
  2. 移除空格后的输入列表必须是平衡的。
*)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition problem_6_pre (input : list Z) : Prop :=
  (ForallChars is_paren_or_space ((string_of_list input))) /\
  (IsBalanced ((string_of_list input))).

Definition problem_6_spec (input output : list Z) : Prop :=
  output = map Z.of_nat (parse_nested_parens_impl (string_of_list input)).

Definition paren_zmax (a b : Z) : Z :=
  if Z.leb a b then b else a.

Definition paren_final_output (out : list Z) (in_group max_level : Z) : list Z :=
  if Z.eqb in_group 0 then out else out ++ [max_level].

Definition paren_step_output (out : list Z) (in_group max_level ch : Z) : list Z :=
  if Z.eqb ch 32 then paren_final_output out in_group max_level else out.

Definition paren_step_in_group (in_group ch : Z) : Z :=
  if Z.eqb ch 32 then 0 else 1.

Definition paren_step_level (in_group level ch : Z) : Z :=
  if Z.eqb ch 32 then
    if Z.eqb in_group 0 then level else 0
  else if Z.eqb ch 40 then level + 1
  else if Z.ltb 0 level then level - 1 else 0.

Definition paren_step_max (in_group level max_level ch : Z) : Z :=
  if Z.eqb ch 32 then
    if Z.eqb in_group 0 then max_level else 0
  else if Z.eqb ch 40 then paren_zmax max_level (level + 1)
  else max_level.

Fixpoint paren_scan_aux
  (chars out : list Z) (in_group level max_level : Z) : list Z * Z * Z * Z :=
  match chars with
  | [] => (out, in_group, level, max_level)
  | ch :: rest =>
      paren_scan_aux rest
        (paren_step_output out in_group max_level ch)
        (paren_step_in_group in_group ch)
        (paren_step_level in_group level ch)
        (paren_step_max in_group level max_level ch)
  end.

Definition paren_state_out (st : list Z * Z * Z * Z) : list Z :=
  match st with (out, _, _, _) => out end.

Definition paren_state_in_group (st : list Z * Z * Z * Z) : Z :=
  match st with (_, in_group, _, _) => in_group end.

Definition paren_state_level (st : list Z * Z * Z * Z) : Z :=
  match st with (_, _, level, _) => level end.

Definition paren_state_max (st : list Z * Z * Z * Z) : Z :=
  match st with (_, _, _, max_level) => max_level end.

Definition paren_prefix_state (i : Z) (input : list Z) : list Z * Z * Z * Z :=
  paren_scan_aux (sublist 0 i input) [] 0 0 0.

Definition paren_prefix_output (i : Z) (input : list Z) : list Z :=
  paren_state_out (paren_prefix_state i input).

Definition paren_prefix_in_group (i : Z) (input : list Z) : Z :=
  paren_state_in_group (paren_prefix_state i input).

Definition paren_prefix_level (i : Z) (input : list Z) : Z :=
  paren_state_level (paren_prefix_state i input).

Definition paren_prefix_max (i : Z) (input : list Z) : Z :=
  paren_state_max (paren_prefix_state i input).

Definition paren_output (input : list Z) : list Z :=
  let st := paren_scan_aux input [] 0 0 0 in
  paren_final_output (paren_state_out st) (paren_state_in_group st) (paren_state_max st).

Fixpoint chars_are_paren_space (l : list Z) : Prop :=
  match l with
  | [] => True
  | x :: xs => (x = 40 \/ x = 41 \/ x = 32) /\ chars_are_paren_space xs
  end.

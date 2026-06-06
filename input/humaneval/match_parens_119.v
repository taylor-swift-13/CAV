(* spec/119 *)
(* You are given a list of two strings, both strings consist of open
parentheses '(' or close parentheses ')' only.
Your job is to check if it is possible to concatenate the two strings in
some order, that the resulting string will be good.
A string S is considered to be good if and only if all parentheses in S
are balanced. For example: the string '(())()' is good, while the string
'())' is not.
Return 'Yes' if there's a way to make a good string, and return 'No' otherwise.

Examples:
match_parens(['()(', ')']) == 'Yes'
match_parens([')', ')']) == 'No' *)

(* 导入 Coq 的标准库 *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(*
  辅助函数 check_parens_inner
*)
Fixpoint check_parens_inner (l : list ascii) (counter : nat) : bool :=
  match l with
  | [] => Nat.eqb counter 0
  | "(" % char :: t => check_parens_inner t (S counter)
  | ")" % char :: t =>
    match counter with
    | 0 => false
    | S n' => check_parens_inner t n'
    end
  | _ :: t => check_parens_inner t counter
  end.

(*
  is_balanced_nat 函数
  修正：现在直接接收一个 list ascii 作为输入。
*)
Definition is_balanced_nat (l : list ascii) : bool :=
  check_parens_inner l 0.

Definition match_parens_impl (inputs : list (list ascii)) : string :=
  match inputs with
  | [s1; s2] =>
    (* "++" 现在是列表拼接操作符 *)
    if orb (is_balanced_nat (s1 ++ s2)) (is_balanced_nat (s2 ++ s1))
    then "Yes"%string
    else "No"%string
  | _ => "No"%string (* 处理非预期输入，例如列表长度不为2 *)
  end.

Definition match_parens (inputs : list string) : string :=
  match_parens_impl (map list_ascii_of_string inputs).

(* 输入列表长度为 2，且每个字符仅为 '(' 或 ')' *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition yesno_of_119 (z : Z) : string :=
  if Z.eqb z 1 then "Yes" else "No".

Definition problem_119_pre (s1 s2 : list Z) : Prop :=
  (length ([string_of_list s1; string_of_list s2]) = 2)%nat /\ Forall (fun s =>
    let l := list_ascii_of_string s in
    Forall (fun c => c = "("%char \/ c = ")"%char) l) ([string_of_list s1; string_of_list s2]).

Definition problem_119_spec (s1 s2 : list Z) (output : Z) : Prop :=
  yesno_of_119 output = match_parens [string_of_list s1; string_of_list s2].

Definition paren_delta (x : Z) : Z :=
  if Z.eqb x 40 then 1 else if Z.eqb x 41 then -1 else 0.

Fixpoint paren_level_upto_nat (n : nat) (l : list Z) : Z :=
  match n with
  | O => 0
  | S n' => paren_level_upto_nat n' l + paren_delta (Znth (Z.of_nat n') l 0)
  end.

Definition paren_level_upto (i : Z) (l : list Z) : Z :=
  paren_level_upto_nat (Z.to_nat i) l.

Fixpoint paren_good_prefix_bool_nat (n : nat) (l : list Z) : bool :=
  match n with
  | O => true
  | S n' =>
      paren_good_prefix_bool_nat n' l &&
      Z.leb 0 (paren_level_upto (Z.of_nat n' + 1) l)
  end.

Definition paren_good_prefix_flag (i : Z) (l : list Z) : Z :=
  if paren_good_prefix_bool_nat (Z.to_nat i) l then 1 else 0.

Definition paren_balanced_by_scan (l : list Z) : bool :=
  Z.eqb (paren_level_upto (Zlength l) l) 0 &&
  Z.eqb (paren_good_prefix_flag (Zlength l) l) 1.

Fixpoint check_parens_z_inner (l : list Z) (counter : Z) : bool :=
  match l with
  | [] => Z.eqb counter 0
  | c :: rest =>
      if Z.eqb c 40 then
        check_parens_z_inner rest (counter + 1)
      else if Z.eqb c 41 then
        if Z.eqb counter 0 then false else check_parens_z_inner rest (counter - 1)
      else
        check_parens_z_inner rest counter
  end.

Definition is_balanced (l : list Z) : bool :=
  check_parens_z_inner l 0.

Fixpoint paren_sum_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | c :: rest => paren_delta c + paren_sum_list rest
  end.

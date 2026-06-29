(* spec/124 *)
(* You have to write a function which validates a given date string and
returns True if the date is valid otherwise False.
The date is valid if all of the following rules are satisfied:
1. The date string is not empty.
2. The number of days is not less than 1 or higher than 31 days for months 1,3,5,7,8,10,12. And the number of days is not less than 1 or higher than 30 days for months 4,6,9,11. And, the number of days is not less than 1 or higher than 29 for the month 2.
3. The months should not be less than 1 or higher than 12.
4. The date should be in the format: mm-dd-yyyy

for example:
valid_date('03-11-2000') => True

valid_date('15-01-2012') => False

valid_date('04-0-2040') => False

valid_date('06-04-2020') => True

valid_date('06/04/2020') => False *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(* 辅助函数：将一个数字字符转换为 nat *)
Definition nat_of_digit (c : ascii) : option nat :=
  match c with
  | "0"%char => Some 0
  | "1"%char => Some 1
  | "2"%char => Some 2
  | "3"%char => Some 3
  | "4"%char => Some 4
  | "5"%char => Some 5
  | "6"%char => Some 6
  | "7"%char => Some 7
  | "8"%char => Some 8
  | "9"%char => Some 9
  | _ => None
  end.

(* 辅助函数：将两个字符转换为 nat *)
Definition nat_of_2_digits (c1 c2 : ascii) : option nat :=
  match (nat_of_digit c1, nat_of_digit c2) with
  | (Some d1, Some d2) => Some (10 * d1 + d2)
  | _ => None
  end.

(* 辅助函数：将四个字符转换为 nat *)
Definition nat_of_4_digits (c1 c2 c3 c4 : ascii) : option nat :=
  match (nat_of_digit c1, nat_of_digit c2, nat_of_digit c3, nat_of_digit c4) with
  | (Some d1, Some d2, Some d3, Some d4) => Some (1000 * d1 + 100 * d2 + 10 * d3 + d4)
  | _ => None
  end.

(* 辅助函数：根据月份返回该月的最大天数 *)
Definition days_in_month_nat (m : nat) : nat :=
  match m with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | 2 => 29 (* 根据规则 #2 *)
  | _ => 0 (* 无效月份 *)
  end.

(* 作为校验函数，输入可为任意字符列表 *)

(*
  程序规约 (Specification)
  这个 Prop 定义了输入的字符列表 s 若满足所有有效日期规则，则为 True。
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition is_digit (x : Z) : Prop :=
  48 <= x <= 57.

Definition is_separator_index (i : Z) : Prop :=
  i = 2 \/ i = 5.

Definition date_char_valid (i : Z) (l : list Z) : Prop :=
  if orb (Z.eqb i 2) (Z.eqb i 5)
  then Znth i l 0 = 45
  else is_digit (Znth i l 0).

Definition date_prefix_valid (i : Z) (l : list Z) : Prop :=
  forall k, 0 <= k < i -> date_char_valid k l.

Definition month (l : list Z) : Z :=
  (Znth 0 l 0 - 48) * 10 + (Znth 1 l 0 - 48).

Definition day (l : list Z) : Z :=
  (Znth 3 l 0 - 48) * 10 + (Znth 4 l 0 - 48).

Definition year (l : list Z) : Z :=
  (Znth 6 l 0 - 48) * 1000 +
  (Znth 7 l 0 - 48) * 100 +
  (Znth 8 l 0 - 48) * 10 +
  (Znth 9 l 0 - 48).

Definition days_in_month (m : Z) : Z :=
  if orb (orb (orb (orb (orb (orb (Z.eqb m 1) (Z.eqb m 3)) (Z.eqb m 5)) (Z.eqb m 7))
              (Z.eqb m 8)) (Z.eqb m 10)) (Z.eqb m 12) then 31
  else if orb (orb (orb (Z.eqb m 4) (Z.eqb m 6)) (Z.eqb m 9)) (Z.eqb m 11) then 30
  else if Z.eqb m 2 then 29
  else 0.

Definition date_format (l : list Z) : Prop :=
  Zlength l = 10 /\
  Znth 2 l 0 = 45 /\
  Znth 5 l 0 = 45 /\
  is_digit (Znth 0 l 0) /\
  is_digit (Znth 1 l 0) /\
  is_digit (Znth 3 l 0) /\
  is_digit (Znth 4 l 0) /\
  is_digit (Znth 6 l 0) /\
  is_digit (Znth 7 l 0) /\
  is_digit (Znth 8 l 0) /\
  is_digit (Znth 9 l 0).

Definition valid_date (l : list Z) : Prop :=
  date_format l /\
  1 <= month l <= 12 /\
  1 <= day l <= days_in_month (month l).

Definition problem_124_pre (s : list Z) : Prop :=
  True.

Definition problem_124_spec (s : list Z) (output : Z) : Prop :=
  output = 1 <-> ((match list_ascii_of_string ((string_of_list s)) with
    (* 模式匹配 "mm-dd-yyyy" 格式。这隐式地检查了列表长度为10 *)
    | [m1; m2; sep1; d1; d2; sep2; y1; y2; y3; y4] =>
        (* 1. 检查分隔符是否为 '-' *)
        sep1 = "-"%char /\ sep2 = "-"%char /\
        (* 尝试将字符解析为月、日、年 *)
        (exists m d y,
          nat_of_2_digits m1 m2 = Some m /\
          nat_of_2_digits d1 d2 = Some d /\
          nat_of_4_digits y1 y2 y3 y4 = Some y /\
          (* 2. 检查月份范围 (1-12) *)
          (1 <= m <= 12 /\
          (* 3. 检查天数范围 (1 到该月最大天数) *)
           1 <= d <= days_in_month_nat m))
    (* 如果字符列表不符合 10 个字符的格式，则直接判定为无效 *)
    | _ => False
    end)%nat).

(* spec/141 *)
(* def file_name_check(file_name):
"""Create a function which takes a string representing a file's name, and returns
'Yes' if the the file's name is valid, and returns 'No' otherwise.
A file's name is considered to be valid if and only if all the following conditions
are met:
- There should not be more than three digits ('0'-'9') in the file's name.
- The file's name contains exactly one dot '.'
- The substring before the dot should not be empty, and it starts with a letter from
the latin alphapet ('a'-'z' and 'A'-'Z').
- The substring after the dot should be one of these: ['txt', 'exe', 'dll']
Examples:
file_name_check("example.txt") # => 'Yes'
file_name_check("1example.dll") # => 'No' (the name should start with a latin alphapet letter)
""" *)
(* 引入必要的库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Import Nat.

(*
  辅助定义（返回 bool）: 检查一个字符是否为数字。
  我们使用 <=? 这个符号，它代表返回 bool 的比较运算。
*)
Definition is_digit_bool (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (nat_of_ascii "0"%char <=? n) && (n <=? nat_of_ascii "9"%char).

(*
  辅助定义（返回 Prop）: 检查一个字符是否为拉丁字母。
*)
Definition is_alpha_nat (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (nat_of_ascii "a"%char <= n /\ n <= nat_of_ascii "z"%char) \/
  (nat_of_ascii "A"%char <= n /\ n <= nat_of_ascii "Z"%char).

(* 输入文件名为任意字符列表，无额外约束 *)

(* file_name_check 函数的程序规约 *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition yesno_of_141 (z : Z) : string :=
  if Z.eqb z 1 then "Yes" else "No".

Definition problem_141_pre (file_name : list Z) : Prop :=
  True.

Definition is_digit (x : Z) : Prop :=
  48 <= x <= 57.

Definition is_digit_zb (x : Z) : bool :=
  Z.leb 48 x && Z.leb x 57.

Definition is_alpha (x : Z) : Prop :=
  65 <= x <= 90 \/ 97 <= x <= 122.

Definition is_dot_zb (x : Z) : bool :=
  Z.eqb x 46.

Fixpoint count_by_zb (f : Z -> bool) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if f x then 1 else 0) + count_by_zb f xs
  end.

Definition digit_count_upto (i : Z) (l : list Z) : Z :=
  count_by_zb is_digit_zb (sublist 0 i l).

Definition dot_count_upto (i : Z) (l : list Z) : Z :=
  count_by_zb is_dot_zb (sublist 0 i l).

Definition suffix_txt (l : list Z) : Prop :=
  Znth (Zlength l - 4) l 0 = 46 /\
  Znth (Zlength l - 3) l 0 = 116 /\
  Znth (Zlength l - 2) l 0 = 120 /\
  Znth (Zlength l - 1) l 0 = 116.

Definition suffix_exe (l : list Z) : Prop :=
  Znth (Zlength l - 4) l 0 = 46 /\
  Znth (Zlength l - 3) l 0 = 101 /\
  Znth (Zlength l - 2) l 0 = 120 /\
  Znth (Zlength l - 1) l 0 = 101.

Definition suffix_dll (l : list Z) : Prop :=
  Znth (Zlength l - 4) l 0 = 46 /\
  Znth (Zlength l - 3) l 0 = 100 /\
  Znth (Zlength l - 2) l 0 = 108 /\
  Znth (Zlength l - 1) l 0 = 108.

Definition suffix_ok (l : list Z) : Prop :=
  suffix_txt l \/ suffix_exe l \/ suffix_dll l.

Definition file_name_checks (l : list Z) : Prop :=
  5 <= Zlength l /\
  is_alpha (Znth 0 l 0) /\
  suffix_ok l /\
  digit_count_upto (Zlength l) l <= 3 /\
  dot_count_upto (Zlength l) l = 1.

Definition problem_141_spec (file_name : list Z) (output : Z) : Prop :=
  (file_name_checks file_name /\ output = 1) \/
  (~ file_name_checks file_name /\ output = 0).

Definition is_dot_ascii_bool (c : ascii) : bool :=
  Ascii.eqb c "."%char.

Definition file_name_valid_ascii_141 (file_name : list ascii) : Prop :=
  (List.length (filter is_digit_bool file_name) <= 3)%nat /\
  exists (prefix suffix : list ascii),
    file_name = (prefix ++ "."%char :: suffix)%list /\
    ~ In "."%char (prefix ++ suffix)%list /\
    (exists first_char rest_prefix,
       prefix = first_char :: rest_prefix /\ is_alpha_nat first_char) /\
    (suffix = ["t"; "x"; "t"]%char \/
     suffix = ["e"; "x"; "e"]%char \/
     suffix = ["d"; "l"; "l"]%char).

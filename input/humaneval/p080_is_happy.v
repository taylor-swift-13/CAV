(* spec/80 *)
(* def is_happy(s):
"""You are given a string s.
Your task is to check if the string is happy or not.
A string is happy if its length is at least 3 and every 3 consecutive letters are distinct
For example:
is_happy(a) => False
is_happy(aa) => False
is_happy(abcd) => True
is_happy(aabb) => False
is_happy(adb) => True
is_happy(xyy) => False
""" *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.

(*
  problem_80_spec s output

  描述了 is_happy 函数的行为，其中输入是一个 ascii 字符列表。
  当且仅当 `output` 是输入列表 `s` 的正确快乐性判断时，该命题为真。

  一个列表是快乐的，当且仅当：
  1. 其长度至少为 3。
  2. 所有连续的 3 个字符都是不同的。
*)

Require Import Coq.ZArith.ZArith.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition problem_80_pre (s : list Z) : Prop :=
  True.

Definition problem_80_spec (s : list Z) (output : Z) : Prop :=
  match bool_of output with
  | true =>
      3 <= Zlength s /\
      forall i, 0 <= i -> i + 2 < Zlength s ->
        Znth i s 0 <> Znth (i + 1) s 0 /\
        Znth i s 0 <> Znth (i + 2) s 0 /\
        Znth (i + 1) s 0 <> Znth (i + 2) s 0
  | false =>
      Zlength s < 3 \/
      exists i, 0 <= i /\ i + 2 < Zlength s /\
        (Znth i s 0 = Znth (i + 1) s 0 \/
         Znth i s 0 = Znth (i + 2) s 0 \/
         Znth (i + 1) s 0 = Znth (i + 2) s 0)
  end.

Definition ascii_range (s : list Z) : Prop :=
  string_bridge.ascii_range s.

Definition happy_window_end (k : Z) (s : list Z) : Prop :=
  Znth k s 0 <> Znth (k - 1) s 0 /\
  Znth k s 0 <> Znth (k - 2) s 0 /\
  Znth (k - 1) s 0 <> Znth (k - 2) s 0.

Definition happy_prefix (i : Z) (s : list Z) : Prop :=
  forall k, 2 <= k < i -> happy_window_end k s.

Definition happy_adjacent (i : Z) (s : list Z) : Prop :=
  Znth (i - 1) s 0 <> Znth (i - 2) s 0.

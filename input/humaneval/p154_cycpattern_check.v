(* spec/154 *)
(* def cycpattern_check(a , b):
"""You are given 2 words. You need to return True if the second word or any of its rotations is a substring in the first word
cycpattern_check("abcd","abd") => False
cycpattern_check("hello","ell") => True
cycpattern_check("whassup","psus") => False
cycpattern_check("abab","baa") => True
cycpattern_check("efef","eeff") => False
cycpattern_check("himenss","simen") => True

""" *)
(* 引入所需的基础库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Import ListNotations.

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

(* 定义：sub 是 main 的子串 *)
Definition is_substring (sub main : list ascii) : Prop :=
  exists prefix suffix, main = prefix ++ sub ++ suffix.

(* 定义：r 是 b 的一个循环旋转 *)
Definition is_rotation_of (r b : list ascii) : Prop :=
  exists p1 p2, b = p1 ++ p2 /\ r = p2 ++ p1.

(* 任意字符串输入，无额外约束 *)

(* cycpattern_check 函数的程序规约 *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition problem_154_pre (a b : list Z) : Prop :=
  True.

Definition rot_index (shift j m : Z) : Z :=
  if (shift + j <? m)%Z then shift + j else shift + j - m.

Definition rotation_prefix
  (pos shift j : Z) (a b : list Z) : Prop :=
  forall k, 0 <= k < j ->
    Znth (pos + k) a 0 =
    Znth (rot_index shift k (Zlength b)) b 0.

Definition rotation_mismatch
  (pos shift j : Z) (a b : list Z) : Prop :=
  exists k, 0 <= k < j /\
    Znth (pos + k) a 0 <>
    Znth (rot_index shift k (Zlength b)) b 0.

Definition rotation_match_progress
  (pos shift j ok : Z) (a b : list Z) : Prop :=
  (ok = 1 -> rotation_prefix pos shift j a b) /\
  (ok = 0 -> rotation_mismatch pos shift j a b).

Definition rotation_match_at_spec
  (pos shift : Z) (a b : list Z) : Prop :=
  0 <= pos /\
  0 <= shift < Zlength b /\
  pos + Zlength b <= Zlength a /\
  rotation_prefix pos shift (Zlength b) a b.

Definition rotation_shift_search
  (shift pos found : Z) (a b : list Z) : Prop :=
  (found = 1 ->
    exists p, 0 <= p < pos /\ rotation_match_at_spec p shift a b) /\
  (found = 0 ->
    forall p, 0 <= p < pos -> ~ rotation_match_at_spec p shift a b).

Definition rotation_shift_has_match
  (shift : Z) (a b : list Z) : Prop :=
  exists p, 0 <= p /\ p + Zlength b <= Zlength a /\
    rotation_match_at_spec p shift a b.

Definition rotation_any_search
  (shift found : Z) (a b : list Z) : Prop :=
  (found = 1 ->
    exists s, 0 <= s < shift /\ rotation_shift_has_match s a b) /\
  (found = 0 ->
    forall s, 0 <= s < shift -> ~ rotation_shift_has_match s a b).

Definition rotation_any_match (a b : list Z) : Prop :=
  Zlength b = 0 \/
  exists s, 0 <= s < Zlength b /\ rotation_shift_has_match s a b.

Definition is_substring_z (sub main : list Z) : Prop :=
  exists prefix suffix, main = (prefix ++ sub ++ suffix)%list.

Definition is_rotation_z (r b : list Z) : Prop :=
  exists p1 p2, b = (p1 ++ p2)%list /\ r = (p2 ++ p1)%list.

Definition problem_154_spec (a b : list Z) (output : Z) : Prop :=
  let la := list_ascii_of_string (string_of_list a) in
  let lb := list_ascii_of_string (string_of_list b) in
  bool_of output = true <-> exists b', is_rotation_of b' lb /\ is_substring b' la.

Definition rotation_bytes (shift : Z) (b : list Z) : list Z :=
  sublist shift (Zlength b) b ++ sublist 0 shift b.

(* spec/93 *)
(*def encode(message):
"""
Write a function that takes a message, and encodes in such a
way that it swaps case of all letters, replaces all vowels in
the message with the letter that appears 2 places ahead of that
vowel in the english alphabet.
Assume only letters.

Examples:
>>> encode('test')
'TGST'
>>> encode('This is a message')
'tHKS KS C MGSSCGG'
""" *)
Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.
Open Scope string_scope. (* 打开作用域以使用 "%char" 表示法 *)

(* 辅助函数：检查一个字符是否是元音 *)
Definition is_vowel_nat (c : ascii) : bool :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char => true
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

(* 辅助函数：转换字母的大小写 *)
Definition swap_case_nat (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if andb (leb 65 n) (leb n 90) (* 是大写字母吗？ *)
  then ascii_of_nat (n + 32) (* 转换为小写 *)
  else if andb (leb 97 n) (leb n 122) (* 是小写字母吗？ *)
  then ascii_of_nat (n - 32) (* 转换为大写 *)
  else c. (* 不是字母，保持原样 *)

(* 辅助函数：将元音替换为两个位置之后的字母 *)
Definition replace_vowel (c : ascii) : ascii :=
  match c with
  | "a"%char => "c"%char | "e"%char => "g"%char | "i"%char => "k"%char | "o"%char => "q"%char | "u"%char => "w"%char
  | "A"%char => "C"%char | "E"%char => "G"%char | "I"%char => "K"%char | "O"%char => "Q"%char | "U"%char => "W"%char
  | _ => c
  end.

Definition encode_char_spec (c_in c_out : ascii) : Prop :=
  let c_swapped := swap_case_nat c_in in
  if is_vowel_nat c_in
  then c_out = replace_vowel c_swapped
  else c_out = c_swapped.

(* 预条件：消息只包含英文字母大小写或空格 *)

(* 完整 encode 函数的规约 *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Export string_bridge.

Local Open Scope Z_scope.

Definition is_upper (c : Z) : Prop := 65 <= c <= 90.
Definition is_lower (c : Z) : Prop := 97 <= c <= 122.
Definition is_space (c : Z) : Prop := c = 32.

Definition problem_93_pre (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s ->
    is_upper (Znth i s 0) \/ is_lower (Znth i s 0) \/ is_space (Znth i s 0).

Definition swap_case (c : Z) : Z :=
  if andb (Z.leb 97 c) (Z.leb c 122) then c - 32
  else if andb (Z.leb 65 c) (Z.leb c 90) then c + 32
  else c.

Definition is_vowel (c : Z) : bool :=
  orb (Z.eqb c 65)
  (orb (Z.eqb c 69)
  (orb (Z.eqb c 73)
  (orb (Z.eqb c 79)
  (orb (Z.eqb c 85)
  (orb (Z.eqb c 97)
  (orb (Z.eqb c 101)
  (orb (Z.eqb c 105)
  (orb (Z.eqb c 111) (Z.eqb c 117))))))))).

Definition encode_char (c : Z) : Z :=
  let w := swap_case c in
  if is_vowel w then w + 2 else w.

Definition problem_93_spec (input output : list Z) : Prop :=
  Zlength output = Zlength input /\
  forall i, 0 <= i < Zlength input ->
    Znth i output 0 = encode_char (Znth i input 0).

Lemma problem_93_pre_char : forall s k,
  problem_93_pre s ->
  ascii_range s ->
  0 <= k < Zlength s ->
  is_upper (Znth k s 0) \/ is_lower (Znth k s 0) \/ is_space (Znth k s 0).
Proof.
  intros s k Hpre _ Hk.
  apply Hpre.
  exact Hk.
Qed.

Lemma encode_char_nonzero : forall c,
  is_upper c \/ is_lower c \/ is_space c ->
  encode_char c <> 0.
Proof.
  intros c Hclass.
  unfold is_upper, is_lower, is_space in Hclass.
  unfold encode_char, swap_case, is_vowel.
  repeat match goal with
  | |- context[Z.leb ?x ?y] =>
      destruct (Z.leb_spec x y); simpl
  | |- context[Z.eqb ?x ?y] =>
      destruct (Z.eqb_spec x y); simpl
  end;
  lia.
Qed.

Lemma problem_93_spec_intro : forall input output n,
  Zlength input = n ->
  Zlength output = n ->
  problem_93_pre input ->
  ascii_range input ->
  (forall k, 0 <= k < n ->
    Znth k output 0 = encode_char (Znth k input 0)) ->
  problem_93_spec input output.
Proof.
  intros input output n Hin Hout _ _ Hpoint.
  unfold problem_93_spec.
  split.
  - lia.
  - intros k Hk.
    apply Hpoint.
    lia.
Qed.

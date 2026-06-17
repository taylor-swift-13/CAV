(* spec/50 *)
(* def encode_shift(s: str):
"""
returns encoded string by shifting every character by 5 in the alphabet.
"""
return "".join([chr(((ord(ch) + 5 - ord("a")) % 26) + ord("a")) for ch in s])

def decode_shift(s: str):
"""
takes as input string encoded with encode_shift function. Returns decoded string.
""" *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith. (* For nat arithmetic like mod *)
Import ListNotations.
Open Scope string_scope.

(* 定义单个字符的解密操作 *)
Definition decode_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  let a := nat_of_ascii "a"%char in
  ascii_of_nat (a + (n - a + 21) mod 26).

Definition is_lowercase_ascii (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (nat_of_ascii "a"%char <= n <= nat_of_ascii "z"%char)%nat.

Fixpoint all_lowercase_ascii (s : string) : Prop :=
  match s with
  | EmptyString => True
  | String c rest => is_lowercase_ascii c /\ all_lowercase_ascii rest
  end.

(* Pre: `decode_shift` is specified for lowercase alphabetic strings. *)

(* decode_shift 程序的规约 *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope Z_scope.

Definition lower_char (c : Z) : Prop := 97 <= c <= 122.

Definition problem_50_pre (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> lower_char (Znth i s 0).

Definition encode_shift_char (c : Z) : Z :=
  Z.rem (c + 5 - 97) 26 + 97.

Definition decode_shift_char (c : Z) : Z :=
  Z.rem (c + 21 - 97) 26 + 97.

Definition problem_50_encode_spec (input output : list Z) : Prop :=
  Zlength output = Zlength input /\
  forall k, 0 <= k < Zlength input ->
    Znth k output 0 = encode_shift_char (Znth k input 0).

Definition problem_50_spec (input output : list Z) : Prop :=
  Zlength output = Zlength input /\
  forall k, 0 <= k < Zlength input ->
    Znth k output 0 = decode_shift_char (Znth k input 0).

Definition problem_50_decode_spec (input output : list Z) : Prop :=
  problem_50_spec input output.

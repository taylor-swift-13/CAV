(* spec/98 *)
(* def count_upper(s):
"""
Given a string s, count the number of uppercase vowels in even indices.

For example:
count_upper('aBCdEf') returns 1
count_upper('abcdefg') returns 0
count_upper('dBBE') returns 0
""" *)

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Open Scope string_scope.
Import ListNotations.

Definition is_uppercase_vowel_bool (c : ascii) : bool :=
  match c with
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Definition count_upper_impl (s : string) : nat :=
  length (filter (fun i : nat =>
    match String.get i s with
    | Some c => andb (Nat.even i) (is_uppercase_vowel_bool c)
    | None => false
    end) (seq 0 (String.length s))).

(* 输入字符串可为任意内容 *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition is_upper_vowel (x : Z) : bool :=
  Z.eqb x 65 || Z.eqb x 69 || Z.eqb x 73 || Z.eqb x 79 || Z.eqb x 85.

Definition is_even_index (i : Z) : bool :=
  Z.eqb (Z.rem i 2) 0.

Fixpoint count_upper_even_upto_nat (n : nat) (l : list Z) : Z :=
  match n with
  | O => 0
  | S n' =>
      let s := count_upper_even_upto_nat n' l in
      let i := Z.of_nat n' in
      if andb (is_even_index i) (is_upper_vowel (Znth i l 0))
      then s + 1
      else s
  end.

Definition count_upper_even_upto (i : Z) (l : list Z) : Z :=
  count_upper_even_upto_nat (Z.to_nat i) l.

Definition problem_98_pre (s : list Z) : Prop :=
  True.

Definition problem_98_spec (s : list Z) (output : Z) : Prop :=
  output = Z.of_nat (count_upper_impl (string_of_list s)).

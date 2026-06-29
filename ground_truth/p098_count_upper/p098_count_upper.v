(* spec/98 *)
(* def count_upper(s):
"""
Given a string s, count the number of uppercase vowels in even indices.

For example:
count_upper('aBCdEf') returns 1
count_upper('abcdefg') returns 0
count_upper('dBBE') returns 0
""" *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.
Import ListNotations.

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

Fixpoint count_upper_even_from (i : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs =>
      (if andb (is_even_index i) (is_upper_vowel x) then 1 else 0) +
      count_upper_even_from (i + 1) xs
  end.

Definition problem_98_pre (s : list Z) : Prop :=
  True.

Definition problem_98_spec (s : list Z) (output : Z) : Prop :=
  output = count_upper_even_from 0 s.

(* spec/64 *)

(* def vowels_count(s):
"""Write a function vowels_count which takes a string representing
a word as input and returns the number of vowels in the string.
Vowels in this case are 'a', 'e', 'i', 'o', 'u'. Here, 'y' is also a
vowel, but only when it is at the end of the given word.

Example:
>>> vowels_count("abcde")
2
>>> vowels_count("ACEDY")
3
""" *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Import ListNotations.

Local Open Scope Z_scope.

Definition is_regular_vowel (x : Z) : bool :=
  Z.eqb x 97 || Z.eqb x 101 || Z.eqb x 105 || Z.eqb x 111 || Z.eqb x 117 ||
  Z.eqb x 65 || Z.eqb x 69 || Z.eqb x 73 || Z.eqb x 79 || Z.eqb x 85.

Definition is_y (x : Z) : bool :=
  Z.eqb x 121 || Z.eqb x 89.

Fixpoint count_regular_vowels_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if is_regular_vowel x then 1 else 0) + count_regular_vowels_list xs
  end.

Definition count_regular_vowels_upto (i : Z) (l : list Z) : Z :=
  count_regular_vowels_list (firstn (Z.to_nat i) l).

Definition last_y_add (l : list Z) : Z :=
  let n := Zlength l in
  if Z.eqb n 0 then 0
  else if is_y (Znth (n - 1) l 0) then 1 else 0.

Definition problem_64_pre (s : list Z) : Prop :=
  True.

Definition problem_64_spec (s : list Z) (output : Z) : Prop :=
  output = count_regular_vowels_list s + last_y_add s.

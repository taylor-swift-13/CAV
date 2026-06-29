(* spec/134 *)
(* def check_if_last_char_is_a_letter(txt):
'''
Create a function that returns True if the last character
of a given string is an alphabetical character and is not
a part of a word, and False otherwise.
Note: "word" is a group of characters separated by space.

Examples:
check_if_last_char_is_a_letter("apple pie") ➞ False
check_if_last_char_is_a_letter("apple pi e") ➞ True
check_if_last_char_is_a_letter("apple pi e ") ➞ False
check_if_last_char_is_a_letter("") ➞ False
''' *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Import ListNotations.

Local Open Scope Z_scope.

Definition is_alpha (x : Z) : Prop :=
  65 <= x <= 90 \/ 97 <= x <= 122.

Definition ascii_range (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0 <= 127.

Definition bool_of (z : Z) : bool :=
  Z.eqb z 1.

Definition ends_with_single_letter (l : list Z) : Prop :=
  1 <= Zlength l /\
  is_alpha (Znth (Zlength l - 1) l 0) /\
  (Zlength l = 1 \/ Znth (Zlength l - 2) l 0 = 32).

Definition problem_134_pre (s : list Z) : Prop :=
  True.

Definition problem_134_spec (s : list Z) (output : Z) : Prop :=
  bool_of output = true <-> ends_with_single_letter s.

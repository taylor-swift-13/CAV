(* spec/54 *)
(* def same_chars(s0: str, s1: str):
"""
Check if two words have the same characters.
>>> same_chars('eabcdzzzz', 'dddzzzzzzzddeddabc')
True
>>> same_chars('abcd', 'dddddddabc')
True
>>> same_chars('dddddddabc', 'abcd')
True
>>> same_chars('eabcd', 'dddddddabc')
False
>>> same_chars('abcd', 'dddddddabce')
False
>>> same_chars('eabcdzzzz', 'dddzzzzzzzddddabc')
False
""" *)
Require Import List Ascii String.
Open Scope string_scope.

(* Pre: no special constraints for `same_chars` *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition problem_54_pre (s0 s1 : list Z) : Prop :=
  True.

Definition no_zero (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> Znth i s 0 <> 0.

Definition char_in (c : Z) (s : list Z) : Prop :=
  In c s.

Definition same_chars_prefix (i : Z) (s0 s1 : list Z) : Prop :=
  forall k, 0 <= k < i -> char_in (Znth k s0 0) s1.

Definition same_chars_all (s0 s1 : list Z) : Prop :=
  same_chars_prefix (Zlength s0) s0 s1.

Definition same_chars_set (s0 s1 : list Z) : Prop :=
  same_chars_all s0 s1 /\ same_chars_all s1 s0.

Definition problem_54_spec (s0 s1 : list Z) (output : Z) : Prop :=
  ((let list_s0 := list_ascii_of_string ((string_of_list s0)) in
    let list_s1 := list_ascii_of_string ((string_of_list s1)) in
    ((bool_of output)) = true <-> (forall (c : ascii), In c list_s0 <-> In c list_s1))%nat).
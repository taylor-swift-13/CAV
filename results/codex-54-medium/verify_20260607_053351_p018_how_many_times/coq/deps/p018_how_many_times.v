(* spec/18 *)
(* """ Find how many times a given substring can be found in the original string. Count overlaping cases.
>>> how_many_times('', 'a')
0
>>> how_many_times('aaa', 'a')
3
>>> how_many_times('aaaa', 'aa')
3
""" *)

(* match_at(i, input, substr) :=
  length(substr) > 0 ∧
  i + length(substr) ≤ length(input) ∧
  ∀ j ∈ [0, length(substr)), input[i + j] = substr[j]

Spec(input, substring, output) :=

​	(∃ index : list(nat),

​		∀ i ∈ [0, length(input)-length(substr)], match_at(i, input, substr) → i ∈ index ) ∧

​    (∀ i ∈ index, match_at(i, input, substr)) ∧

​	output = length(index) *)

Require Import List.
Import ListNotations.
Require Import Ascii.
Require Import String.
Require Import Nat.
Open Scope string_scope.

(* 表示从 input 的第 i 位开始，与 substr 完全匹配 *)
Definition match_at (i : nat) (input substr : string) : Prop :=
  String.length substr > 0 /\
  i + String.length substr <= String.length input /\
  (forall j, j < String.length substr -> String.get (i + j) input = String.get j substr).

(* Spec: output是input中substring出现的次数 *)
(* Pre: no additional constraints for `how_many_times` by default *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition ascii_range (s : list Z) : Prop :=
  string_bridge.ascii_range s.

Definition problem_18_pre (input substring : list Z) : Prop :=
  True.

Definition match_prefix (i j : Z) (input substring : list Z) : Prop :=
  forall k, 0 <= k < j ->
    Znth (i + k) input 0 = Znth k substring 0.

Definition mismatch_prefix (i j : Z) (input substring : list Z) : Prop :=
  exists k, 0 <= k < j /\
    Znth (i + k) input 0 <> Znth k substring 0.

Definition match_progress
  (i j ok : Z) (input substring : list Z) : Prop :=
  (ok = 1 -> match_prefix i j input substring) /\
  (ok = 0 -> mismatch_prefix i j input substring).

Fixpoint list_eq_zb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => Z.eqb x y && list_eq_zb xs ys
  | _, _ => false
  end.

Definition match_at_zb (i : Z) (input substring : list Z) : bool :=
  (Z.ltb 0 (Zlength substring)) &&
  (Z.leb (i + Zlength substring) (Zlength input)) &&
  list_eq_zb (sublist i (i + Zlength substring) input) substring.

Fixpoint count_matches_upto_nat
  (fuel : nat) (input substring : list Z) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      count_matches_upto_nat fuel' input substring +
      if match_at_zb (Z.of_nat fuel') input substring then 1 else 0
  end.

Definition count_matches_upto
  (i : Z) (input substring : list Z) : Z :=
  count_matches_upto_nat (Z.to_nat i) input substring.

Definition problem_18_spec (input substring : list Z) (output : Z) : Prop :=
  output = count_matches_upto (Zlength input) input substring.

Fixpoint matching_indices_nat
  (fuel : nat) (input substring : list Z) : list nat :=
  match fuel with
  | O => nil
  | S fuel' =>
      if match_at_zb (Z.of_nat fuel') input substring
      then fuel' :: matching_indices_nat fuel' input substring
      else matching_indices_nat fuel' input substring
  end.

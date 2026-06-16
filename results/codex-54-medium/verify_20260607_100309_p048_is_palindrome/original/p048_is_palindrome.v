(* spec/48 *)
(* Checks if given string is a palindrome
>>> is_palindrome('')
True
>>> is_palindrome('aba')
True
>>> is_palindrome('aaaaa')
True
>>> is_palindrome('zbcd')
False *)

(* Spec(input : string, output : bool) :=
​ output = true ↔ ∀i ∈ [0, length(input) / 2), input[i] = input[length(input) - 1 - i] *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
From AUXLib Require Import ListLib.
Import ListNotations.

Local Open Scope Z_scope.

Definition problem_48_pre (input : list Z) : Prop :=
  True.

Definition bool_of (z : Z) : bool :=
  Z.eqb z 1.

Definition palindrome (input : list Z) : Prop :=
  forall k,
    0 <= k < Zlength input ->
    k < Zlength input - 1 - k ->
    Znth k input 0 = Znth (Zlength input - 1 - k) input 0.

Definition problem_48_spec (input : list Z) (output : Z) : Prop :=
  bool_of output = true <-> palindrome input.

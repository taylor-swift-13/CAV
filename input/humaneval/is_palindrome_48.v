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

Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.

(* Pre: no special constraints for `is_palindrome` *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition problem_48_pre (input : list Z) : Prop :=
  True.

Definition palindrome (input : list Z) : Prop :=
  forall k,
    0 <= k < Zlength input ->
    k < Zlength input - 1 - k ->
    Znth k input 0 = Znth (Zlength input - 1 - k) input 0.

Definition problem_48_spec (input : list Z) (output : Z) : Prop :=
  (((*
      ((bool_of output)) 为 true 当且仅当 (<->) 以下条件成立:
      对于所有自然数 i，如果 i 小于字符串长度的一半，
      那么在 i 位置的字符必须等于在 (length - 1 - i) 位置的字符。
    *)
    ((bool_of output)) = true <-> (forall (i : nat),
      (i < (String.length ((string_of_list input))) / 2)%nat ->
      String.get i ((string_of_list input)) = String.get (String.length ((string_of_list input)) - 1 - i) ((string_of_list input))))%nat).
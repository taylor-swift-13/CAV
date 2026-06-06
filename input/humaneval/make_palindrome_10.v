(* spec/10 *)
(* Find the shortest palindrome that begins with a supplied string.
Algorithm idea is simple:
- Find the longest postfix of supplied string that is a palindrome.
- Append to the end of the string reverse of a string prefix that comes before the palindromic suffix.
>>> make_palindrome('')
''
>>> make_palindrome('cat')
'catac'
>>> make_palindrome('cata')
'catac'
*)

(* Spec(input, output) :=

prefix(input, output) ∧
palindrome(output) ∧
∀ p, 
  (prefix(input, p) ∧ palindrome(p)) → length(output) ≤ length(p)) *)

From Coq Require Import Ascii String List Arith Lia.
Import ListNotations.
Open Scope string_scope.

(* 回文定义：反转后等于自己 *)
Definition palindrome (s : string) : Prop :=
  s = string_of_list_ascii (List.rev (list_ascii_of_string s)).


(* 规格定义：最短的回文，且以 input 为前缀 *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition problem_10_pre (input : list Z) : Prop :=
  True.

Definition problem_10_spec (input output : list Z) : Prop :=
  ((prefix ((string_of_list input)) ((string_of_list output)) = true /\
    palindrome ((string_of_list output)) /\
   forall p : string,
      prefix ((string_of_list input)) p = true /\
      palindrome p ->
      String.length ((string_of_list output)) <= String.length p)%nat).

Definition pal_suffix (start : Z) (input : list Z) : Prop :=
  0 <= start <= Zlength input /\
  forall k,
    0 <= k < Zlength input - start ->
    k < Zlength input - start - 1 - k ->
    Znth (start + k) input 0 = Znth (Zlength input - 1 - k) input 0.

Definition first_pal_suffix (best : Z) (input : list Z) : Prop :=
  0 <= best <= Zlength input /\
  pal_suffix best input /\
  forall t, 0 <= t < best -> ~ pal_suffix t input.

Definition make_pal_output (best : Z) (input : list Z) : list Z :=
  input ++ rev (firstn (Z.to_nat best) input).

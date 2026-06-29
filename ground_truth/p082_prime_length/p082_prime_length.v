(* spec/82 *)
(* def prime_length(string):
"""Write a function that takes a string and returns True if the string
length is a prime number or False otherwise
Examples
prime_length('Hello') == True
prime_length('abcdcba') == True
prime_length('kittens') == True
prime_length('orange') == False
""" *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
From AUXLib Require Import ListLib.
Import ListNotations.

Local Open Scope Z_scope.

Definition prime_prefix (i n : Z) : Prop :=
  forall d, 2 <= d < i -> Z.rem n d <> 0.

Definition prime_len (n : Z) : Prop :=
  2 <= n /\ forall d, 2 <= d /\ d * d <= n -> Z.rem n d <> 0.

Definition bool_of (z : Z) : bool :=
  Z.eqb z 1.

Definition problem_82_pre (s : list Z) : Prop :=
  True.

Definition problem_82_spec (s : list Z) (output : Z) : Prop :=
  bool_of output = true <-> prime_len (Zlength s).

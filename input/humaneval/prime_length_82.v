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
(* 导入 Coq 标准库，用于字符串和自然数算术 *)
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.



Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition prime_prefix (i n : Z) : Prop :=
  forall d, 2 <= d < i -> Z.rem n d <> 0.

Definition prime_len (n : Z) : Prop :=
  2 <= n /\ forall d, 2 <= d /\ d * d <= n -> Z.rem n d <> 0.

Definition problem_82_pre (s : list Z) : Prop :=
  True.

Definition problem_82_spec (s : list Z) (output : Z) : Prop :=
  ((((bool_of output)) = true <-> prime (Z.of_nat (String.length ((string_of_list s)))))%nat).
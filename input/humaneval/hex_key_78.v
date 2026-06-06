(* spec/78 *)

(* def hex_key(num):
"""You have been tasked to write a function that receives
a hexadecimal number as a string and counts the number of hexadecimal
digits that are primes (prime number, or a prime, is a natural number
greater than 1 that is not a product of two smaller natural numbers).
Hexadecimal digits are 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, A, B, C, D, E, F.
Prime numbers are 2, 3, 5, 7, 11, 13, 17,...
So you have to determine a number of the following digits: 2, 3, 5, 7,
B (=decimal 11), D (=decimal 13).
Note: you may assume the input is always correct or empty string,
and symbols A,B,C,D,E,F are always uppercase.
Examples:
For num = "AB" the output should be 1.
For num = "1077E" the output should be 2.
For num = "ABED1A33" the output should be 4.
For num = "123456789ABCDEF0" the output should be 6.
For num = "2020" the output should be 2.
""" *)

Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition is_prime_hex_digit (c : ascii) : bool :=
  match c with
  | "2"%char | "3"%char | "5"%char | "7"%char
  | "B"%char | "D"%char => true
  | _ => false
  end.

Fixpoint count_prime_hex (s : string) : nat :=
  match s with
  | "" => 0
  | String h t =>
    (if is_prime_hex_digit h then 1 else 0) +
    count_prime_hex t
  end.

Definition hex_key_impl (s : string) : nat :=
  count_prime_hex s.



Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition is_prime_hex (x : Z) : bool :=
  Z.eqb x 50 || Z.eqb x 51 || Z.eqb x 53 ||
  Z.eqb x 55 || Z.eqb x 66 || Z.eqb x 68.

Fixpoint count_prime_hex_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if is_prime_hex x then 1 else 0) + count_prime_hex_list xs
  end.

Definition count_prime_hex_upto (i : Z) (l : list Z) : Z :=
  count_prime_hex_list (firstn (Z.to_nat i) l).

Definition problem_78_pre (s : list Z) : Prop :=
  True.

Definition problem_78_spec (s : list Z) (output : Z) : Prop :=
  output = Z.of_nat (hex_key_impl (string_of_list s)).

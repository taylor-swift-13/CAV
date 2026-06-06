(* spec/139 *)
(* def special_factorial(n):
"""The Brazilian factorial is defined as:
brazilian_factorial(n) = n! * (n-1)! * (n-2)! * ... * 1!
where n > 0

For example:
>>> special_factorial(4)
288

The function will receive an integer as input and should return the special
factorial of this integer.
""" *)

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Import ListNotations.

Fixpoint fact (n : nat) : nat :=
  match n with
  | 0 => 1
  | S k => n * fact k
  end.

Definition brazilian_factorial_impl (n : nat) : nat :=
  fold_right mult 1 (map fact (seq 1 n)).

(* n > 0 *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Fixpoint factorial_nat (n : nat) : Z :=
  match n with
  | O => 1
  | S k => Z.of_nat (S k) * factorial_nat k
  end.

Fixpoint bfact_nat (n : nat) : Z :=
  match n with
  | O => 1
  | S k => bfact_nat k * factorial_nat (S k)
  end.

Definition factorial (n : Z) : Z := factorial_nat (Z.to_nat n).
Definition bfact_coq (n : Z) : Z := bfact_nat (Z.to_nat n).

Definition problem_139_pre (n : Z) : Prop := n > 0.
Definition problem_139_spec (n r : Z) : Prop :=
  r = bfact_coq n.

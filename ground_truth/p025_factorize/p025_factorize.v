(* spec/25 *)
(* """ Return list of prime factors of given integer in the order from smallest to largest.
Each of the factors should be listed number of times corresponding to how many times it appeares in factorization.
Input number should be equal to the product of all factors
>>> factorize(8)
[2, 2, 2]
>>> factorize(25)
[5, 5]
>>> factorize(70)
[2, 5, 7]
""" *)

(* Spec(input : int, output : list int) :=

​	IsSorted(output) ∧

​	Multiply(output) = input ∧

​	∀i ∈ output, IsPrime(i) *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

(* Pre: no additional constraints for `factorize` by default *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

From AUXLib Require Import ListLib.

Local Open Scope Z_scope.

Definition problem_25_pre (n : Z) : Prop :=
  True.

Definition zprod (l : list Z) : Z :=
  fold_right Z.mul 1 l.

Definition zprime (n : Z) : Prop :=
  IsPrime (Z.to_nat n).

Definition problem_25_spec (n : Z) (output : list Z) : Prop :=
  Sorted Z.le output /\
  zprod output = n /\
  Forall zprime output.

Definition no_small_factor (n i : Z) : Prop :=
  forall d, 2 <= d < i -> Z.rem n d <> 0.

Definition factorize_loop_state
  (n0 n i : Z) (factors : list Z) : Prop :=
  2 <= n <= n0 /\
  2 <= i <= n0 /\
  Zlength factors + n <= n0 /\
  Forall (fun x => 2 <= x <= n0) factors /\
  zprod factors * n = n0 /\
  Sorted Z.le factors /\
  Forall zprime factors /\
  Forall (fun x => x <= i) factors /\
  Forall (fun x => x <= n) factors /\
  no_small_factor n i.

(* spec/106 *)
(* Implement the function f that takes n as a parameter,
and returns a list of size n, such that the value of the element at index i is the factorial of i if i is even
or the sum of numbers from 1 to i otherwise.
i starts from 1.
the factorial of i is the multiplication of the numbers from 1 to i (1 * 2 * ... * i).
Example:
f(5) == [1, 2, 6, 24, 15] *)

(* 引入 Coq 的自然数和列表库 *)
Require Import Nat.
Require Import List.
Import ListNotations.

(* n 为自然数，无额外约束 *)


Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Fixpoint triangular_nat (n : nat) : nat :=
  match n with
  | O => O
  | S k => triangular_nat k + S k
  end.

Definition problem_106_pre (n : Z) : Prop :=
  0 <= n.

Fixpoint triangular_fuel (fuel : nat) (i : Z) : Z :=
  match fuel with
  | O => 0
  | S fuel' => if Z.leb i 0 then 0 else triangular_fuel fuel' (i - 1) + i
  end.

Fixpoint factorial_fuel_106 (fuel : nat) (i : Z) : Z :=
  match fuel with
  | O => 1
  | S fuel' => if Z.leb i 1 then 1 else i * factorial_fuel_106 fuel' (i - 1)
  end.

Definition triangular (i : Z) : Z :=
  triangular_fuel (Z.to_nat i) i.

Definition factorial (i : Z) : Z :=
  factorial_fuel_106 (Z.to_nat i) i.

Definition f_elem (i : Z) : Z :=
  if Z.even i then factorial i else triangular i.

Definition f_seq (n : Z) : list Z :=
  map (fun i => f_elem (i + 1)) (Zseq 0 (Z.to_nat n)).

Definition problem_106_spec (n : Z) (out : list Z) : Prop :=
  0 <= n /\ out = f_seq n.

Definition f_seq_int_range (n : Z) : Prop :=
  forall i,
    1 <= i <= n ->
    INT_MIN <= i <= INT_MAX /\
    INT_MIN <= triangular i <= INT_MAX /\
    INT_MIN <= factorial i <= INT_MAX.

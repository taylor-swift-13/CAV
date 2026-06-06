(* spec/130 *)
(* def tri_nat(n):
"""Everyone knows Fibonacci sequence, it was studied deeply by mathematicians in
the last couple centuries. However, what people don't know is Tribonacci sequence.
Tribonacci sequence is defined by the recurrence:
tri_nat(1) = 3
tri_nat(n) = 1 + n / 2, if n is even.
tri_nat(n) = tri_nat(n - 1) + tri_nat(n - 2) + tri_nat(n + 1), if n is odd.
For example:
tri_nat(2) = 1 + (2 / 2) = 2
tri_nat(4) = 3
tri_nat(3) = tri_nat(2) + tri_nat(1) + tri_nat(4)
= 2 + 3 + 3 = 8
You are given a non-negative integer number n, you have to a return a list of the
first n + 1 numbers of the Tribonacci sequence.
Examples:
tri_nat(3) = [1, 3, 2, 8]
""" *)
Require Import Arith.
Require Import List.
Import ListNotations.

(* 使用Fixpoint来实现Tribonacci序列的计算 *)
Fixpoint tri_nat (n : nat) : nat :=
  match n with
  | 0 => 1
  | 1 => 3
  | S (S k) =>
      if Nat.even n then
        1 + n / 2
      else
        let t_prev := 1 + (n - 1) / 2 in
        let t_next := 1 + (n + 1) / 2 in
        t_prev + tri_nat k + t_next
  end.

(* n 为非负整数（nat 已满足），无额外约束 *)

(* 定义tri函数的程序规约 *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Fixpoint tri_fuel (fuel : nat) (i : Z) : Z :=
  match fuel with
  | O => if Z.eqb i 1 then 3 else 1
  | S fuel' =>
      if Z.eqb i 0 then 1
      else if Z.eqb i 1 then 3
      else if Z.even i then 1 + Z.quot i 2
      else (1 + Z.quot (i - 1) 2) + tri_fuel fuel' (i - 2) +
           (1 + Z.quot (i + 1) 2)
  end.

Definition tri (i : Z) : Z :=
  tri_fuel (Z.to_nat i) i.

Definition tri_sequence (n : Z) : list Z :=
  map tri (Zseq 0 (Z.to_nat (n + 1))).

Definition problem_130_pre (n : Z) : Prop :=
  0 <= n.

Definition problem_130_spec (n : Z) (out : list Z) : Prop :=
  0 <= n /\ out = tri_sequence n.

Definition tri_seq_int_range (n : Z) : Prop :=
  (forall i, 0 <= i <= n -> INT_MIN <= tri i <= INT_MAX) /\
  (forall i, 2 <= i <= n ->
     INT_MIN <= 1 + Z.quot i 2 <= INT_MAX /\
     INT_MIN <= tri (i - 1) + tri (i - 2) + 1 + Z.quot (i + 1) 2 <= INT_MAX).

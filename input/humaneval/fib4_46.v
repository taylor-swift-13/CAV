(* spec/46 *)
(* The Fib4 number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows:
fib4_nat(0) -> 0
fib4_nat(1) -> 0
fib4_nat(2) -> 2
fib4_nat(3) -> 0
fib4_nat(n) -> fib4_nat(n-1) + fib4_nat(n-2) + fib4_nat(n-3) + fib4_nat(n-4).
Please write a function to efficiently compute the n-th element of the fib4_nat number sequence. Do not use recursion.
>>> fib4_nat(5)
4
>>> fib4_nat(6)
8
>>> fib4_nat(7)
14 *)

(* 
  Spec(input : int, output : int) :=

​	∃ Fib : list int,
​		Fib[0] = 0 /\ Fib[1] = 0 /\ Fib[2] = 2 /\ Fib[3] = 0 /\
​		∀i ∈ N, i >3 → Fib[i] = Fib[i-1] + Fib[i-2] + Fib[i-3] + Fib[i-4] /\
​		output = Fib[input] *)

Require Import Coq.Arith.Arith.

(* 使用 Fixpoint 表示 fib4_nat 序列 *)
Fixpoint fib4_nat (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n1 =>
    match n1 with
    | 0 => 0
    | S n2 =>
      match n2 with
      | 0 => 2
      | S n3 =>
        match n3 with
        | 0 => 0
        | S n4 => fib4_nat n1 + fib4_nat n2 + fib4_nat n3 + fib4_nat n4
        end
      end
    end
  end.



Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition fib4 (n : Z) : Z :=
  Z.of_nat (fib4_nat (Z.to_nat n)).

Definition problem_46_pre (n : Z) : Prop :=
  0 <= n.

Definition problem_46_spec (n output : Z) : Prop :=
  0 <= n /\ output = fib4 n.

Definition fib4_step_int_range (n : Z) : Prop :=
  forall i,
    4 <= i <= n ->
    INT_MIN <= fib4 (i - 4) + fib4 (i - 3) <= INT_MAX /\
    INT_MIN <= fib4 (i - 4) + fib4 (i - 3) + fib4 (i - 2) <= INT_MAX /\
    INT_MIN <= fib4 (i - 4) + fib4 (i - 3) + fib4 (i - 2) + fib4 (i - 1) <= INT_MAX.

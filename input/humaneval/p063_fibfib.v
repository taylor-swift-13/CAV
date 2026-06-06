(* spec/63 *)
(* def fibfib_nat(n: int):
"""The FibFib number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows:
fibfib_nat(0) == 0
fibfib_nat(1) == 0
fibfib_nat(2) == 1
fibfib_nat(n) == fibfib_nat(n-1) + fibfib_nat(n-2) + fibfib_nat(n-3).
Please write a function to efficiently compute the n-th element of the fibfib_nat number sequence.
>>> fibfib_nat(1)
0
>>> fibfib_nat(5)
4
>>> fibfib_nat(8)
24
""" *)
(* 引入Coq中关于自然数的基础库 *)
Require Import Coq.Init.Nat.

Fixpoint fibfib_nat (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    match n' with
    | 0 => 0
    | S n'' =>
      match n'' with
      | 0 => 1
      | S n''' => fibfib_nat n' + fibfib_nat n'' + fibfib_nat n'''
      end
    end
  end.

(*
  problem_63_spec 是对 fibfib 函数的程序规约。

  它指出，一个函数若要满足此规约，其对于任何输入 n，
  必须返回一个结果 res，使得 res = fibfib_nat n。

  参数：
  - n: nat    (代表程序的输入)
  - res: nat  (代表程序的输出)
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Fixpoint fibfib_fuel (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O =>
      if Z.eqb n 2 then 1 else 0
  | S fuel' =>
      if Z.eqb n 0 then 0
      else if Z.eqb n 1 then 0
      else if Z.eqb n 2 then 1
      else fibfib_fuel fuel' (n - 1) + fibfib_fuel fuel' (n - 2) +
           fibfib_fuel fuel' (n - 3)
  end.

Definition fibfib (n : Z) : Z :=
  fibfib_fuel (Z.to_nat n) n.

Definition problem_63_pre (n : Z) : Prop :=
  0 <= n.

Definition problem_63_spec (n res : Z) : Prop :=
  0 <= n /\ res = fibfib n.

Definition fibfib_step_int_range (n : Z) : Prop :=
  forall i,
    3 <= i <= n ->
    INT_MIN <= fibfib (i - 3) + fibfib (i - 2) <= INT_MAX /\
    INT_MIN <= fibfib (i - 3) + fibfib (i - 2) + fibfib (i - 1) <= INT_MAX.

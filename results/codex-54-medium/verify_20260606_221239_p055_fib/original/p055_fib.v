(* spec/55 *)
(* def fib(n: int):
Return n-th Fibonacci number.
>>> fib(10)
55
>>> fib(1)
1
>>> fib(8)
21
*)
(* 引入Coq标准库，用于自然数（nat）的定义 *)
Require Import Coq.Init.Nat.

(*
  fib 是一个递归函数，定义了斐波那契数列。
*)
Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
    | 0 => 1
    | S n'' => fib n'' + fib n'
    end
  end.

(*
  fib_spec 是对 fib 函数的程序规约。

  参数：
  - n: nat    (代表程序的输入)
  - res: nat  (代表程序的输出)

*)
(* Pre: no special constraints for `fib` *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Fixpoint fib_seq_fuel (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => if Z.eqb n 0 then 0 else 1
  | S fuel' =>
      if Z.eqb n 0 then 0
      else if Z.eqb n 1 then 1
      else fib_seq_fuel fuel' (n - 1) + fib_seq_fuel fuel' (n - 2)
  end.

Definition fib_seq (n : Z) : Z :=
  fib_seq_fuel (Z.to_nat n) n.

Definition problem_55_pre (n : Z) : Prop :=
  0 <= n.

Definition problem_55_spec (n res : Z) : Prop :=
  0 <= n /\ res = fib_seq n.

Definition fib_step_int_range (n : Z) : Prop :=
  forall i,
    2 <= i <= n ->
    INT_MIN <= fib_seq (i - 2) + fib_seq (i - 1) <= INT_MAX.

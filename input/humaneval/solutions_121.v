(* spec/121 *)
(* Given a non-empty list of integers, return the sum of all of the odd elements that are in even positions.
Examples
solution([5, 8, 7, 1]) ==> 12
solution([3, 3, 3, 3, 3]) ==> 9
solution([30, 13, 24, 321]) ==>0*)

Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.

Fixpoint sum_odd_in_even_pos_aux (l : list nat) (idx : nat) : nat :=
  match l with
  | [] => 0
  | h::t => (if (Nat.even idx) && negb (Nat.even h) then h else 0) + sum_odd_in_even_pos_aux t (S idx)
  end.

Definition sum_odd_in_even_pos_impl (l : list nat) : nat := sum_odd_in_even_pos_aux l 0.

(* 非空整数列表 *)


Require Import Coq.ZArith.ZArith.
Require Import Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Fixpoint sum_odd_at_even_upto_nat (n : nat) (l : list Z) : Z :=
  match n with
  | O => 0
  | S n' =>
      let s := sum_odd_at_even_upto_nat n' l in
      let i := Z.of_nat n' in
      let x := Znth (2 * i) l 0 in
      if Z.eqb (Z.rem x 2) 1 then s + x else s
  end.

Definition sum_odd_at_even_upto (i : Z) (l : list Z) : Z :=
  sum_odd_at_even_upto_nat (Z.to_nat i) l.

Definition problem_121_pre (lst : list Z) : Prop :=
  lst <> [].

Definition problem_121_spec (lst : list Z) (output : Z) : Prop :=
  output = sum_odd_at_even_upto (Zlength lst) lst.

Definition odd_even_position_add (x : Z) : Z :=
  if Z.eqb (Z.rem x 2) 1 then x else 0.

Fixpoint sum_odd_in_even_positions (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: [] => odd_even_position_add x
  | x :: _ :: rest => odd_even_position_add x + sum_odd_in_even_positions rest
  end.

Fixpoint sum_odd_in_even_positions_nat (l : list nat) : nat :=
  match l with
  | [] => O
  | x :: [] => if Nat.odd x then x else O
  | x :: _ :: rest => (if Nat.odd x then x else O) + sum_odd_in_even_positions_nat rest
  end.

Definition sum_odd_at_even_int_range (lst : list Z) : Prop :=
  forall i,
    0 <= i ->
    2 * i < Zlength lst ->
    INT_MIN <= sum_odd_at_even_upto i lst <= INT_MAX /\
    INT_MIN <= sum_odd_at_even_upto i lst + Znth (2 * i) lst 0 <= INT_MAX.

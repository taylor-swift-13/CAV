(* spec/142 *)
(* def sum_squares(lst):
This function will take a list of integers. For all entries in the list, the function shall square the integer entry if its index is a
multiple of 3 and will cube the integer entry if its index is a multiple of 4 and not a multiple of 3. The function will not
change the entries in the list whose indexes are not a multiple of 3 or 4. The function shall then return the sum of all entries.

Examples:
For lst = [1,2,3] the output should be 6
For lst = [] the output should be 0
For lst = [-1,-5,2,-1,-5] the output should be -126
 *)

Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.NArith.NArith Coq.Bool.Bool.
Import ListNotations.

Fixpoint sum_transformed (l : list Z) (n : nat) : Z :=
  match l with
  | [] => 0%Z
  | h :: t =>
      let transformed :=
        if (Nat.modulo n 3 =? 0%nat) then (Z.mul h h)
        else if andb (Nat.modulo n 4 =? 0%nat) (negb (Nat.modulo n 3 =? 0%nat)) then Z.mul (Z.mul h h) h
        else h in
      Z.add transformed (sum_transformed t (S n))
  end.

Definition sum_squares_impl (lst : list Z) : Z := sum_transformed lst 0%nat.

(* 任意整数列表（允许为空） *)


Require Import Coq.ZArith.Zquot.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition transformed_value (i x : Z) : Z :=
  if Z.rem i 3 =? 0 then x * x
  else if Z.rem i 4 =? 0 then x * x * x
  else x.

Fixpoint transformed_sum_from (l : list Z) (start : Z) : Z :=
  match l with
  | nil => 0
  | x :: xs => transformed_value start x + transformed_sum_from xs (start + 1)
  end.

Definition transformed_prefix_sum (i : Z) (l : list Z) : Z :=
  transformed_sum_from (sublist 0 i l) 0.

Definition problem_142_pre (l : list Z) : Prop :=
  True.

Definition problem_142_spec (l : list Z) (out : Z) : Prop :=
  out = sum_squares_impl l.

Definition sum_squares_int_range (l : list Z) : Prop :=
  (forall i,
     0 <= i < Zlength l ->
     let x := Znth i l 0 in
     INT_MIN <= x * x <= INT_MAX /\
     INT_MIN <= x * x * x <= INT_MAX /\
     INT_MIN <= transformed_prefix_sum i l + transformed_value i x <= INT_MAX) /\
  (forall i, 0 <= i <= Zlength l -> INT_MIN <= transformed_prefix_sum i l <= INT_MAX).

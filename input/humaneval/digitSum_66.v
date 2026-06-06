(* spec/66 *)
(* def digitSum(s):
Task
Write a function that takes a string as input and returns the sum of the upper characters only'
ASCII codes.

Examples:
digitSum("") => 0
digitSum("abAB") => 131
digitSum("abcCd") => 67
digitSum("helloE") => 69
digitSum("woArBld") => 131
digitSum("aAaaaXa") => 153 *)

Require Import Coq.Strings.Ascii Coq.Lists.List Coq.Strings.String.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

Definition is_uppercase (c : ascii) : bool :=
  let n := nat_of_ascii c in (Nat.leb 65 n) && (Nat.leb n 90).

Fixpoint sum_uppercase_ascii (s : string) : nat :=
  match s with
  | "" => 0
  | String c s' => if is_uppercase c then nat_of_ascii c + sum_uppercase_ascii s'
              else sum_uppercase_ascii s'
  end.

Definition digitSum_impl (s : string) : nat := sum_uppercase_ascii s.



Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import string_bridge.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition is_upper (x : Z) : bool :=
  (Z.leb 65 x) && (Z.leb x 90).

Fixpoint sum_upper_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if is_upper x then x else 0) + sum_upper_list xs
  end.

Definition sum_upper_upto (i : Z) (l : list Z) : Z :=
  sum_upper_list (firstn (Z.to_nat i) l).

Definition problem_66_pre (s : list Z) : Prop :=
  True.

Definition problem_66_spec (s : list Z) (output : Z) : Prop :=
  output = Z.of_nat (digitSum_impl (string_of_list s)).

Definition digit_sum_int_range (s : list Z) : Prop :=
  forall i,
    0 <= i ->
    i < Zlength s ->
    INT_MIN <= sum_upper_upto i s <= INT_MAX /\
    INT_MIN <= sum_upper_upto i s + Znth i s 0 <= INT_MAX.

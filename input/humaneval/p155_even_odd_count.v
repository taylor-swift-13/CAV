(* spec/155 *)
(* def even_odd_count(num):
"""Given an integer. return a tuple that has the number of even and odd digits respectively.

Example:
even_odd_count(-12) ==> (1, 1)
even_odd_count(123) ==> (1, 2)
""" *)

Require Import Coq.Lists.List Coq.Strings.Ascii Coq.ZArith.ZArith Coq.Arith.Arith.
Open Scope Z_scope.

Fixpoint count_digits_acc (l : list Z) (acc : nat * nat) : nat * nat :=
  match l with
  | nil => acc
  | h :: t =>
      let '(e,o) := acc in
      if Z.even h
      then count_digits_acc t (S e, o)
      else count_digits_acc t (e, S o)
  end.

Fixpoint to_digits_fuel_nonzero (fuel : nat) (n : Z) : list Z :=
  match fuel with
  | O => nil
  | S f' =>
      let p := Z.abs n in
      if p =? 0 then nil else (p mod 10) :: to_digits_fuel_nonzero f' (p / 10)
  end.

Definition to_digits (n : Z) : list Z :=
  if Z.abs n =? 0
  then 0 :: nil
  else to_digits_fuel_nonzero (Z.to_nat (Z.abs n) + 1)%nat n.

Definition even_odd_count_impl (num : Z) : nat * nat :=
  count_digits_acc (to_digits num) (0%nat, 0%nat).

(* 任意整数输入 *)


Require Import Coq.ZArith.Zquot.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.

Definition Zabs (x : Z) : Z := Z.abs x.

Fixpoint c_digits_fuel (fuel : nat) (n : Z) : list Z :=
  match fuel with
  | O => nil
  | S fuel' =>
      let p := Z.abs n in
      if p =? 0 then nil else Z.rem p 10 :: c_digits_fuel fuel' (Z.quot p 10)
  end.

Definition c_digits (n : Z) : list Z :=
  if Z.abs n =? 0
  then [0]
  else c_digits_fuel (Z.to_nat (Z.abs n) + 1)%nat (Z.abs n).

Fixpoint count_digits_c (digits : list Z) (even odd : Z) : Z * Z :=
  match digits with
  | nil => (even, odd)
  | d :: rest =>
      if Z.eqb (Z.rem d 2) 1
      then count_digits_c rest even (odd + 1)
      else count_digits_c rest (even + 1) odd
  end.

Definition count_result_c (num : Z) : Z * Z :=
  count_digits_c (c_digits num) 0 0.

Definition digit_count_state (num w even odd : Z) : Prop :=
  0 <= w /\
  0 <= even /\
  0 <= odd /\
  exists fuel,
    (w = 0 \/ w < Z.of_nat fuel) /\
    count_digits_c (c_digits_fuel fuel w) even odd = count_result_c num /\
    even + odd + Zlength (c_digits_fuel fuel w) <= Z.abs num + 1.

Definition problem_155_pre (num : Z) : Prop :=
  True.

Definition problem_155_spec (num : Z) (output : list Z) : Prop :=
  exists even odd,
      output = [Z.of_nat even; Z.of_nat odd] /\
      (((even, odd)) = even_odd_count_impl num).

(* Helper lemmas migrated from the old proof, with names aligned to the input spec. *)

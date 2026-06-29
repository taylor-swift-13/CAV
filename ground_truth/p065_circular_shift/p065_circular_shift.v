(* spec/65 *)
(* def circular_shift(x, shift):
"""Circular shift the digits of the integer x, shift the digits right by shift
and return the result as a string.
If shift > number of digits, return digits reversed.
>>> circular_shift(12, 1)
"21"
>>> circular_shift(12, 2)
"12"
""" *)
(* 导入所需的标准库 *)
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

Fixpoint to_digits_fuel (n fuel : nat) : list nat :=
  match fuel with
  | O => []
  | S fuel' =>
      if (n <? 10)%nat then
        [n]
      else
        (to_digits_fuel (n / 10) fuel') ++ [n mod 10]
  end.

Definition to_digits (n : nat) : list nat :=
  if (n =? 0)%nat then
    [0]
  else
    to_digits_fuel n n.

Definition digit_to_string (d : nat) : string :=
  match d with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9"
  | _ => ""
  end.

Fixpoint from_digits_to_string (l : list nat) : string :=
  match l with
  | [] => ""
  | h :: t => (digit_to_string h) ++ (from_digits_to_string t)
  end.

Definition circular_shift_impl (x : nat) (shift : nat) : string :=
  let digits := to_digits x in
  let len := length digits in
  if (x =? 0)%nat then
    "0"
  else
    if (len <? shift)%nat then
      from_digits_to_string (rev digits)
    else
      let effective_shift := shift mod len in
      if (effective_shift =? 0)%nat then
        from_digits_to_string digits
      else
        let split_point := len - effective_shift in
        let new_head := skipn split_point digits in
        let new_tail := firstn split_point digits in
        from_digits_to_string (new_head ++ new_tail).



Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.
Require Import Recdef.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
Require Import base_conversion_lib.
Require Import string_bridge.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition problem_65_pre (x shift : Z) : Prop :=
  True.

Definition decimal_digits (x : Z) : list Z :=
  map (fun d => 48 + Z.of_nat d) (to_digits (Z.to_nat x)).

Definition circular_shift_index (len shift i : Z) : Z :=
  if Z.ltb len shift then len - 1 - i else (len - shift + i) mod len.

Definition circular_shift_output (x shift : Z) : list Z :=
  let digits := decimal_digits x in
  let len := Zlength digits in
  if Z.ltb len shift then
    rev digits
  else
    sublist (len - shift) len digits ++ sublist 0 (len - shift) digits.

Definition problem_65_spec (x shift : Z) (output : list Z) : Prop :=
  output = circular_shift_output x shift.

Definition circular_shift_prefix
  (x shift i : Z) (out_l : list Z) : Prop :=
  out_l = sublist 0 i (circular_shift_output x shift).

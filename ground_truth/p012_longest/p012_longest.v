(* """ Out of list of strings, return the longest one. Return the first one in case of multiple
strings of the same length. Return None in case the input list is empty.
>>> longest([])

>>> longest(['a', 'b', 'c'])
'a'
>>> longest(['a', 'bb', 'ccc'])
'ccc'
""" *)

(* Spec(input, output) :=
  (length(input) = 0 ∧ output = None) ∨
  (length(input) > 0 ∧
    ∃ i ∈ [0, length(input)),
      output = input[i] ∧
      ∀ j ∈ [0, length(input)), length(input[j]) ≤ length(output) ∧
      ∀ j ∈ [0, i), length(input[j]) < length(output)
  )
 *)

Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no specific requirements for `longest` — accept any list of strings by default *)
Definition problem_12_pre (input : list string) : Prop := True.

Definition problem_12_spec (input : list string) (output : option string) : Prop :=
  (input = [] /\ output = None) \/
  (exists out i,
    output = Some out /\
    List.length input > 0 /\
    i < List.length input /\
    nth_error input i = Some out /\
    (forall j, j < List.length input -> exists s, nth_error input j = Some s -> String.length s <= String.length out) /\
    (forall j, j < i -> exists s, nth_error input j = Some s -> String.length s < String.length out)
  ).

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition ascii_of_z_12 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_12 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_12 c) (string_of_list_z_12 rest)
  end.

Definition row_payload_z_12 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_12 (row : list Z) : string :=
  string_of_list_z_12 (row_payload_z_12 row).

Definition rows_to_strings_z_12 (rows : list (list Z)) : list string :=
  map row_string_z_12 rows.

Definition row_len_z_12 (row : list Z) : Z :=
  string_length (row_payload_z_12 row).

Definition problem_12_pre_z (rows : list (list Z)) : Prop :=
  problem_12_pre (rows_to_strings_z_12 rows).

Definition problem_12_spec_none_z (rows : list (list Z)) : Prop :=
  problem_12_spec (rows_to_strings_z_12 rows) None.

Definition problem_12_spec_some_z (rows : list (list Z)) (best_idx : Z) : Prop :=
  problem_12_spec
    (rows_to_strings_z_12 rows)
    (Some (row_string_z_12 (Znth best_idx rows nil))).

Definition rows_well_formed_12 (rows : list (list Z)) (n : Z) : Prop :=
  Zlength rows = n /\
  forall k,
    0 <= k < n ->
    let row := Znth k rows nil in
    let payload := row_payload_z_12 row in
    row = c_string payload /\
    valid_string payload /\
    string_length payload < INT_MAX.

Definition longest_prefix_z_12
    (rows : list (list Z)) (k best_idx best_len : Z) : Prop :=
  0 <= k <= Zlength rows /\
  ((k = 0 /\ best_idx = -1 /\ best_len = -1) \/
   (0 < k /\
    0 <= best_idx < k /\
    best_len = row_len_z_12 (Znth best_idx rows nil) /\
    (forall j,
       0 <= j < k ->
       row_len_z_12 (Znth j rows nil) <= best_len) /\
    (forall j,
       0 <= j < best_idx ->
       row_len_z_12 (Znth j rows nil) < best_len))).

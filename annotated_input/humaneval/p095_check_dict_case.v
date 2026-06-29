(*def check_dict_case(dict):
"""
Given a dictionary, return True if all keys are strings in lower
case or all keys are strings in upper case, else return False.
The function should return False is the given dictionary is empty.
Examples:
check_dict_case({"a":"apple", "b":"banana"}) should return True.
check_dict_case({"a":"apple", "A":"banana", "B":"banana"}) should return False.
check_dict_case({"a":"apple", 8:"banana", "a":"apple"}) should return False.
check_dict_case({"Name":"John", "Age":"36", "City":"Houston"}) should return False.
check_dict_case({"STATE":"NC", "ZIP":"12345" }) should return True.
"""*)
Require Import Coq.Strings.String Bool.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

(* 定义字符串是否为小写的谓词 *)
Definition is_lowercase (s : string) : Prop :=
  Forall (fun c => (("a" <=? c)%char && (c <=? "z")%char) = true) (list_ascii_of_string s).

(* 定义字符串是否为大写的谓词 *)
Definition is_uppercase (s : string) : Prop :=
  Forall (fun c => (("A" <=? c)%char && (c <=? "Z")%char) = true) (list_ascii_of_string s).

(* 定义键的类型，可以是字符串或其他类型 *)
Inductive KeyType :=
  | KeyString (s : string)
  | KeyOther.

(* 定义字典的类型，键为 KeyType，值为字符串 *)
Definition dictionary := list (KeyType * string).

(* 字典类型已保证键值均为字符串，无附加约束；空字典由规约处理 *)
Definition problem_95_pre (d : dictionary) : Prop := True.

(* check_dict_case 函数的规约 *)
Definition problem_95_spec (d : dictionary) (output : bool) : Prop :=
  match d with
  | [] => output = false
  | _ =>
    ( (forall k v, In (k, v) d -> match k with KeyString s => is_lowercase s | KeyOther => False end) \/
      (forall k v, In (k, v) d -> match k with KeyString s => is_uppercase s | KeyOther => False end) )
    <-> output = true
  end.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.NArith.NArith.
Require Import Lia.
From AUXLib Require Import ListLib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition ascii_of_z (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z c) (string_of_list_z rest)
  end.

Definition bool_of_z (z : Z) : bool :=
  Z.eqb z 1.

Definition row_payload_z (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition rows_to_dictionary_z (rows : list (list Z)) : dictionary :=
  map (fun row => (KeyString (string_of_list_z (row_payload_z row)), EmptyString)) rows.

Definition problem_95_pre_z (rows : list (list Z)) : Prop :=
  problem_95_pre (rows_to_dictionary_z rows).

Definition lower_char_z (c : Z) : Prop :=
  97 <= c <= 122.

Definition upper_char_z (c : Z) : Prop :=
  65 <= c <= 90.

Definition letter_char_z (c : Z) : Prop :=
  upper_char_z c \/ lower_char_z c.

Definition payload_index_z (row : list Z) (i : Z) : Prop :=
  0 <= i < Zlength row - 1.

Definition row_all_lower_z (row : list Z) : Prop :=
  forall i, payload_index_z row i -> lower_char_z (Znth i row 0).

Definition row_all_upper_z (row : list Z) : Prop :=
  forall i, payload_index_z row i -> upper_char_z (Znth i row 0).

Definition row_all_letters_z (row : list Z) : Prop :=
  forall i, payload_index_z row i -> letter_char_z (Znth i row 0).

Definition rows_all_lower_z (rows : list (list Z)) : Prop :=
  forall k, 0 <= k < Zlength rows -> row_all_lower_z (Znth k rows nil).

Definition rows_all_upper_z (rows : list (list Z)) : Prop :=
  forall k, 0 <= k < Zlength rows -> row_all_upper_z (Znth k rows nil).

Definition rows_have_uniform_case_z (rows : list (list Z)) : Prop :=
  rows_all_lower_z rows \/ rows_all_upper_z rows.

Definition scanned_position_z (k i r j : Z) : Prop :=
  (0 <= r < k /\ 0 <= j) \/ (r = k /\ 0 <= j < i).

Definition scanned_char_z (rows : list (list Z)) (k i r j : Z) : Prop :=
  0 <= r < Zlength rows /\
  scanned_position_z k i r j /\
  j < Zlength (Znth r rows nil) - 1.

Definition scanned_all_letters_z (rows : list (list Z)) (k i : Z) : Prop :=
  forall r j,
    scanned_char_z rows k i r j ->
    letter_char_z (Znth j (Znth r rows nil) 0).

Definition scanned_has_lower_z (rows : list (list Z)) (k i : Z) : Prop :=
  exists r j,
    scanned_char_z rows k i r j /\
    lower_char_z (Znth j (Znth r rows nil) 0).

Definition scanned_has_upper_z (rows : list (list Z)) (k i : Z) : Prop :=
  exists r j,
    scanned_char_z rows k i r j /\
    upper_char_z (Znth j (Znth r rows nil) 0).

Definition scan_state_z (rows : list (list Z)) (k i islower isupper : Z) : Prop :=
  scanned_all_letters_z rows k i /\
  (islower = 1 <-> scanned_has_lower_z rows k i) /\
  (isupper = 1 <-> scanned_has_upper_z rows k i) /\
  0 <= islower <= 1 /\
  0 <= isupper <= 1 /\
  islower + isupper <= 1.

Definition invalid_char_seen_z (rows : list (list Z)) (k i : Z) : Prop :=
  0 <= k < Zlength rows /\
  payload_index_z (Znth k rows nil) i /\
  ~ letter_char_z (Znth i (Znth k rows nil) 0).

Definition mixed_case_seen_z (rows : list (list Z)) (k i : Z) : Prop :=
  scanned_has_lower_z rows k i /\ scanned_has_upper_z rows k i.

Definition problem_95_spec_z (rows : list (list Z)) (ret : Z) : Prop :=
  problem_95_spec (rows_to_dictionary_z rows) (bool_of_z ret).

Definition rows_well_formed_z (rows : list (list Z)) (dict_size : Z) : Prop :=
  Zlength rows = dict_size /\
  forall k,
    0 <= k < dict_size ->
    0 < Zlength (Znth k rows nil) <= 101 /\
    Znth (Zlength (Znth k rows nil) - 1) (Znth k rows nil) 0 = 0 /\
    (forall i, payload_index_z (Znth k rows nil) i ->
       0 <= Znth i (Znth k rows nil) 0 <= 127 /\
       Znth i (Znth k rows nil) 0 <> 0).

Definition dictionary_all_lower_z (rows : list (list Z)) : Prop :=
  forall k v,
    In (k, v) (rows_to_dictionary_z rows) ->
    match k with
    | KeyString s => is_lowercase s
    | KeyOther => False
    end.

Definition dictionary_all_upper_z (rows : list (list Z)) : Prop :=
  forall k v,
    In (k, v) (rows_to_dictionary_z rows) ->
    match k with
    | KeyString s => is_uppercase s
    | KeyOther => False
    end.

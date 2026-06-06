(* spec/86 *)
(* def anti_shuffle(s):
"""
Write a function that takes a string and returns an ordered version of it.
Ordered version of string, is a string where all words (separated by space)
are replaced by a new word where all the characters arranged in
ascending order based on ascii value.
Note: You should keep the order of words and blank spaces in the sentence.

For example:
anti_shuffle('Hi') returns 'Hi'
anti_shuffle('hello') returns 'ehllo'
anti_shuffle('Hello World!!!') returns 'Hello !!!Wdlor'
""" *)
(* 引入 Coq 标准库中关于字符串、列表、算术和置换的理论 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope string_scope.

Definition is_space_bool (c : ascii) : bool :=
  if ascii_dec c " "%char then true else false.

Fixpoint insert_char_nat (c : ascii) (s : string) : string :=
  match s with
  | EmptyString => String c EmptyString
  | String h t =>
      if Nat.leb (nat_of_ascii c) (nat_of_ascii h) then
        String c s
      else
        String h (insert_char_nat c t)
  end.

Fixpoint sort_chars_nat (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String h t => insert_char_nat h (sort_chars_nat t)
  end.

Fixpoint anti_shuffle_aux (s : string) (acc : string) : string :=
  match s with
  | EmptyString => sort_chars_nat acc
  | String c rest =>
      if is_space_bool c then
        (sort_chars_nat acc) ++ (String c EmptyString) ++ (anti_shuffle_aux rest EmptyString)
      else
        anti_shuffle_aux rest (String c acc)
  end.

Definition anti_shuffle_impl (s : string) : string :=
  anti_shuffle_aux s EmptyString.



Require Import Coq.ZArith.ZArith.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition problem_86_pre (s : list Z) : Prop :=
  True.

Definition empty_z_list : list Z := [].

Definition is_space (c : Z) : bool :=
  Z.eqb c 32.

Definition ascii_le (a b : Z) : bool :=
  Nat.leb (nat_of_ascii (ascii_of a)) (nat_of_ascii (ascii_of b)).

Fixpoint insert_char (c : Z) (l : list Z) : list Z :=
  match l with
  | [] => [c]
  | h :: t =>
      if ascii_le c h then c :: l else h :: insert_char c t
  end.

Fixpoint sort_chars_forward (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => insert_char h (sort_chars_forward t)
  end.

Definition sort_chars (l : list Z) : list Z :=
  sort_chars_forward (rev l).

Definition anti_step_state (st : list Z * list Z) (c : Z) : list Z * list Z :=
  let '(out_l, cur_l) := st in
  if is_space c then
    (out_l ++ sort_chars cur_l ++ [32], [])
  else
    (out_l, cur_l ++ [c]).

Fixpoint anti_state_nat (n : nat) (l : list Z) : list Z * list Z :=
  match n with
  | O => ([], [])
  | S n' => anti_step_state (anti_state_nat n' l) (Znth (Z.of_nat n') l 0)
  end.

Definition anti_out_prefix (i : Z) (l : list Z) : list Z :=
  fst (anti_state_nat (Z.to_nat i) l).

Definition anti_cur_prefix (i : Z) (l : list Z) : list Z :=
  snd (anti_state_nat (Z.to_nat i) l).

Definition anti_shuffle_output (l : list Z) : list Z :=
  anti_out_prefix (Zlength l) l ++ sort_chars (anti_cur_prefix (Zlength l) l).

Definition problem_86_spec (s output : list Z) : Prop :=
  string_of_list output = anti_shuffle_impl (string_of_list s).

Fixpoint anti_process (l cur : list Z) : list Z :=
  match l with
  | [] => sort_chars cur
  | c :: rest =>
      if is_space c then
        sort_chars cur ++ [32] ++ anti_process rest []
      else
        anti_process rest (cur ++ [c])
  end.

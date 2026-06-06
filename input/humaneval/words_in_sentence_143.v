(* spec/143 *)
(* def words_in_sentence(sentence):
"""
You are given a string representing a sentence,
the sentence contains some words separated by a space,
and you have to return a string that contains the words from the original sentence,
whose lengths are prime numbers,
the order of the words in the new string should be the same as the original one.

Example 1:
Input: sentence = "This is a test"
Output: "is"

Example 2:
Input: sentence = "lets go for swimming"
Output: "go for"

Constraints:
* 1 <= len(sentence) <= 100
* sentence contains only letters
""" *)

Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.

Fixpoint has_divisor_from (n d : nat) : bool :=
  match d with
  | 0 => false
  | 1 => false
  | S d' =>
    if (n mod d =? 0)%nat then
      true
    else
      has_divisor_from n d'
  end.

Definition is_prime_bool (n : nat) : bool :=
  match n with
  | 0 | 1 => false
  | _ => negb (has_divisor_from n (n - 1))
  end.

Definition split_words_nat (s : list ascii) : list (list ascii) :=
  let space := " "%char in
  let fix aux (cur : list ascii) (rest : list ascii) : list (list ascii) :=
    match rest with
    | [] =>
      match cur with
      | [] => []
      | _ => [rev cur]
      end
    | h :: t =>
      if Ascii.eqb h space then
        match cur with
        | [] => aux [] t
        | _ => (rev cur) :: aux [] t
        end
      else
        aux (h :: cur) t
    end
  in aux [] s.

Fixpoint join_words_nat (ws : list (list ascii)) : list ascii :=
  match ws with
  | [] => []
  | w :: nil => w
  | w :: rest =>
    w ++ (" "%char :: nil) ++ join_words_nat rest
  end.

Definition words_in_sentence_impl (sentence : string) : string :=
  let words := split_words_nat (list_ascii_of_string sentence) in
  let sel := List.filter (fun w => is_prime_bool (List.length w)) words in
  string_of_list_ascii (join_words_nat sel).

(* 约束：1 <= 长度 <= 100；内容为英文字母或空格 *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition problem_143_pre (sentence : list Z) : Prop :=
  let l := list_ascii_of_string ((string_of_list sentence)) in
  (1 <= List.length l /\ List.length l <= 100)%nat /\
  Forall (fun c =>
    let n := Z.of_nat (nat_of_ascii c) in c = " "%char \/ (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122)) l.

Definition problem_143_spec (sentence output : list Z) : Prop :=
  string_of_list output = words_in_sentence_impl (string_of_list sentence).

Definition ascii_range (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> 0 <= Znth i s 0 <= 127.

Definition z_of_ascii (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c).

Fixpoint list_z_of_string (s : string) : list Z :=
  match s with
  | EmptyString => []
  | String c rest => z_of_ascii c :: list_z_of_string rest
  end.

Definition prime_len_flag (n : Z) : Z :=
  if is_prime_bool (Z.to_nat n) then 1 else 0.

Fixpoint split_words_z_aux (cur rest : list Z) : list (list Z) :=
  match rest with
  | [] =>
      match cur with
      | [] => []
      | _ => [rev cur]
      end
  | h :: t =>
      if Z.eqb h 32 then
        match cur with
        | [] => split_words_z_aux [] t
        | _ => rev cur :: split_words_z_aux [] t
        end
      else split_words_z_aux (h :: cur) t
  end.

Definition split_words (sentence : list Z) : list (list Z) :=
  split_words_z_aux [] sentence.

Fixpoint split_words_ascii_aux (cur rest : list ascii) : list (list ascii) :=
  match rest with
  | [] =>
      match cur with
      | [] => []
      | _ => [rev cur]
      end
  | h :: t =>
      if Ascii.eqb h " "%char then
        match cur with
        | [] => split_words_ascii_aux [] t
        | _ => rev cur :: split_words_ascii_aux [] t
        end
      else split_words_ascii_aux (h :: cur) t
  end.

Definition split_words_ascii (sentence : list ascii) : list (list ascii) :=
  split_words_ascii_aux [] sentence.

Definition split_words_spec_aux (cur rest : list ascii) : list (list ascii) :=
  (fix aux (cur rest : list ascii) {struct rest} : list (list ascii) :=
     match rest with
     | [] =>
         match cur with
         | [] => []
         | _ => [rev cur]
         end
     | h :: t =>
         if Ascii.eqb h " "%char then
           match cur with
           | [] => aux [] t
           | _ => rev cur :: aux [] t
           end
         else aux (h :: cur) t
     end) cur rest.

Definition words_output_ascii (s : list ascii) : list ascii :=
  join_words_nat
    (List.filter (fun w => is_prime_bool (List.length w)) (split_words_nat s)).

Fixpoint join_words (ws : list (list Z)) : list Z :=
  match ws with
  | [] => []
  | w :: nil => w
  | w :: rest => w ++ [32] ++ join_words rest
  end.

Definition selected_words (sentence : list Z) : list (list Z) :=
  List.filter (fun w => Z.eqb (prime_len_flag (Zlength w)) 1)
    (split_words sentence).

Definition words_in_sentence_output (sentence : list Z) : list Z :=
  join_words (selected_words sentence).

Definition words_in_sentence_prefix (i : Z) (sentence : list Z) : list Z :=
  words_in_sentence_output (sublist 0 i sentence).

Definition prime_loop_state (n j composite : Z) : Prop :=
  composite = 1 <->
    exists d, 2 <= d < j /\ Z.rem n d = 0.

Definition append_selected_word
    (out prefix : list Z) (start len : Z) : list Z :=
  if Z.eqb (prime_len_flag len) 1 then
    out ++ (if Z.eqb (Zlength out) 0 then [] else [32]) ++
    sublist start (start + len) prefix
  else out.

Definition word_chars (sentence : list Z) (start i : Z) : Prop :=
  forall p, start <= p < i -> Znth p (sentence ++ [0]) 0 <> 32.

Definition word_start (sentence : list Z) (start : Z) : Prop :=
  start = 0 \/ Znth (start - 1) (sentence ++ [0]) 0 = 32.

Definition scan_ready (sentence : list Z) (len i : Z) : Prop :=
  i = 0 \/
  i = len \/
  Znth i (sentence ++ [0]) 0 = 32 \/
  Znth (i - 1) (sentence ++ [0]) 0 = 32.

Definition word_copy_prefix (start k : Z) (sentence : list Z) : list Z :=
  words_in_sentence_prefix start sentence ++
  (if Z.eqb (Zlength (words_in_sentence_prefix start sentence)) 0
   then [] else [32]) ++
  sublist start (start + k) sentence.

Definition nonspace_z_list (w : list Z) : Prop :=
  forall x, In x w -> x <> 32.

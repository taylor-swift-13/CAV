Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition lower_ascii (c : Z) : Z :=
  if Z.leb 65 c then
    if Z.leb c 90 then c - 65 + 97 else c
  else c.

Definition is_alpha (c : Z) : bool :=
  if Z.leb 65 c then
    if Z.leb c 90 then true
    else if Z.leb 97 c then Z.leb c 122 else false
  else if Z.leb 97 c then Z.leb c 122 else false.

Fixpoint all_alpha (l : list Z) : Prop :=
  match l with
  | [] => True
  | c :: rest => is_alpha c = true /\ all_alpha rest
  end.

Definition alpha_word (l : list Z) : Prop :=
  l <> [] /\ all_alpha l.

Fixpoint valid_candidate_stream_aux (l : list Z) (in_word : bool) : Prop :=
  match l with
  | [] => if in_word then True else False
  | c :: rest =>
      if Z.eqb c 59
      then in_word = true /\ valid_candidate_stream_aux rest false
      else is_alpha c = true /\ valid_candidate_stream_aux rest true
  end.

Definition valid_candidate_stream (l : list Z) : Prop :=
  match l with
  | [] => True
  | _ => valid_candidate_stream_aux l false
  end.

Fixpoint take_word (l : list Z) : list Z :=
  match l with
  | [] => []
  | c :: rest => if Z.eqb c 59 then [] else c :: take_word rest
  end.

Fixpoint drop_word_sep (l : list Z) : list Z :=
  match l with
  | [] => []
  | c :: rest => if Z.eqb c 59 then rest else drop_word_sep rest
  end.

Fixpoint split_candidates_aux (l : list Z) (fuel : nat) : list (list Z) :=
  match fuel with
  | O => []
  | S fuel' =>
      match l with
      | [] => []
      | _ => take_word l :: split_candidates_aux (drop_word_sep l) fuel'
      end
  end.

Definition split_candidates (l : list Z) : list (list Z) :=
  split_candidates_aux l (List.length l).

Fixpoint list_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => Z.eqb x y && list_eqb xs ys
  | _, _ => false
  end.

Definition equal_ignore_caseb (a b : list Z) : bool :=
  list_eqb (map lower_ascii a) (map lower_ascii b).

Fixpoint count_lower_char (target : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | c :: rest =>
      (if Z.eqb (lower_ascii c) target then 1 else 0) +
      count_lower_char target rest
  end.

Fixpoint same_letter_multisetb_aux
         (fuel : nat) (idx : Z) (a b : list Z) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
      Z.eqb (count_lower_char idx a) (count_lower_char idx b) &&
      same_letter_multisetb_aux fuel' (idx + 1) a b
  end.

Definition same_letter_multisetb (a b : list Z) : bool :=
  same_letter_multisetb_aux 26%nat 97 a b.

Definition is_anagram_candidateb (subject cand : list Z) : bool :=
  negb (equal_ignore_caseb subject cand) &&
  same_letter_multisetb subject cand.

Fixpoint count_anagram_candidates
         (subject : list Z) (cands : list (list Z)) : Z :=
  match cands with
  | [] => 0
  | cand :: rest =>
      (if is_anagram_candidateb subject cand then 1 else 0) +
      count_anagram_candidates subject rest
  end.

Definition ex_anagram_count_pre
           (subject candidates : list Z) : Prop :=
  alpha_word subject /\ valid_candidate_stream candidates.

Definition ex_anagram_count_spec
           (subject candidates : list Z) : Z :=
  count_anagram_candidates subject (split_candidates candidates).

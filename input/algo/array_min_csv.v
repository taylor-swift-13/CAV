Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition is_digit (c : Z) : bool :=
  andb (48 <=? c) (c <=? 57).

Fixpoint parse_digits (l : list Z) (acc : Z) : Z :=
  match l with
  | [] => acc
  | c :: rest => parse_digits rest (acc * 10 + (c - 48))
  end.

Fixpoint split_at_comma (l : list Z) : list Z * list Z :=
  match l with
  | [] => ([], [])
  | c :: rest =>
      if Z.eqb c 44 then ([], rest)
      else
        let '(before, after) := split_at_comma rest in
        (c :: before, after)
  end.

Fixpoint split_csv_tokens_aux (l : list Z) (fuel : nat) : list (list Z) :=
  match fuel with
  | O => []
  | S fuel' =>
      match l with
      | [] => []
      | _ =>
          let '(tok, rest) := split_at_comma l in
          tok :: split_csv_tokens_aux rest fuel'
      end
  end.

Definition split_csv_tokens (l : list Z) : list (list Z) :=
  split_csv_tokens_aux l (List.length l).

Fixpoint digit_chars (l : list Z) : Prop :=
  match l with
  | [] => True
  | c :: rest => 48 <= c <= 57 /\ digit_chars rest
  end.

Definition valid_token (tok : list Z) : Prop :=
  match tok with
  | [] => True
  | 45 :: [] => True
  | 45 :: ds => digit_chars ds /\ parse_digits ds 0 <= 2147483647
  | _ => digit_chars tok /\ parse_digits tok 0 <= 2147483647
  end.

Fixpoint all_valid_tokens (toks : list (list Z)) : Prop :=
  match toks with
  | [] => True
  | tok :: rest => valid_token tok /\ all_valid_tokens rest
  end.

Definition trim_trailing_empty_token (toks : list (list Z)) : list (list Z) :=
  match rev toks with
  | [] => []
  | [] :: rest_rev => rev rest_rev
  | _ => toks
  end.

Definition parse_token (tok : list Z) : Z :=
  match tok with
  | [] => 0
  | 45 :: [] => 0
  | 45 :: ds => - parse_digits ds 0
  | _ => parse_digits tok 0
  end.

Definition parse_csv_impl (l : list Z) : list Z :=
  map parse_token (trim_trailing_empty_token (split_csv_tokens l)).

Definition array_min_csv_pre (l : list Z) : Prop :=
  all_valid_tokens (split_csv_tokens l).

Definition list_min_aux (t : list Z) (h : Z) : Z :=
  fold_left Z.min t h.

Definition array_min_csv_spec (l : list Z) : Z :=
  match parse_csv_impl l with
  | h :: t => list_min_aux t h
  | _ => 0
  end.

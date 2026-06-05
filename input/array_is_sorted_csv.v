Require Import ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.

Fixpoint parse_digits (l : list Z) (acc : Z) : Z :=
  match l with
  | nil => acc
  | d :: rest => parse_digits rest (acc * 10 + d - 48)
  end.

Fixpoint split_at_comma (l : list Z) : list Z * list Z :=
  match l with
  | nil => (nil, nil)
  | x :: rest =>
      if Z.eqb x 44 then (nil, rest)
      else
        let '(before, after) := split_at_comma rest in
        (x :: before, after)
  end.

Definition parse_token (tok : list Z) : Z :=
  match tok with
  | 45 :: ds => - parse_digits ds 0
  | _ => parse_digits tok 0
  end.

Definition parse_one_int (l : list Z) : Z * list Z :=
  let '(tok, rest) := split_at_comma l in
  (parse_token tok, rest).

Fixpoint parse_csv_aux (l : list Z) (fuel : nat) : list Z :=
  match fuel with
  | O => nil
  | S n =>
      match l with
      | nil => nil
      | _ =>
          let '(v, rest) := parse_one_int l in
          v :: parse_csv_aux rest n
      end
  end.

Definition parse_csv (l : list Z) : list Z :=
  parse_csv_aux l (List.length l).

Fixpoint is_sorted_z (l : list Z) : bool :=
  match l with
  | nil => true
  | _ :: nil => true
  | x :: (y :: _ as rest) =>
      if Z.leb x y then is_sorted_z rest else false
  end.

Fixpoint digit_chars (l : list Z) : Prop :=
  match l with
  | nil => True
  | x :: rest => 48 <= x <= 57 /\ digit_chars rest
  end.

Definition valid_token (tok : list Z) : Prop :=
  match tok with
  | nil => False
  | 45 :: ds =>
      ds <> nil /\
      digit_chars ds /\
      parse_digits ds 0 <= 2147483647
  | _ =>
      digit_chars tok /\
      parse_digits tok 0 <= 2147483647
  end.

Fixpoint split_csv_tokens_aux (l : list Z) (fuel : nat) : list (list Z) :=
  match fuel with
  | O => nil
  | S n =>
      match l with
      | nil => nil
      | _ =>
          let '(tok, rest) := split_at_comma l in
          tok :: split_csv_tokens_aux rest n
      end
  end.

Definition split_csv_tokens (l : list Z) : list (list Z) :=
  split_csv_tokens_aux l (List.length l).

Fixpoint all_valid_tokens (toks : list (list Z)) : Prop :=
  match toks with
  | nil => True
  | tok :: rest => valid_token tok /\ all_valid_tokens rest
  end.

Definition starts_with_comma (l : list Z) : Prop :=
  match l with
  | nil => False
  | x :: _ => x = 44
  end.

Fixpoint ends_with_comma (l : list Z) : Prop :=
  match l with
  | nil => False
  | x :: nil => x = 44
  | _ :: rest => ends_with_comma rest
  end.

Fixpoint no_adjacent_commas (l : list Z) : Prop :=
  match l with
  | nil => True
  | x :: rest =>
      match rest with
      | nil => True
      | y :: _ =>
          (x = 44 -> y <> 44) /\
          no_adjacent_commas rest
      end
  end.

Definition array_is_sorted_csv_pre (l : list Z) : Prop :=
  match l with
  | nil => True
  | _ =>
      ~ starts_with_comma l /\
      ~ ends_with_comma l /\
      no_adjacent_commas l /\
      all_valid_tokens (split_csv_tokens l)
  end.

Definition array_is_sorted_csv_spec (l : list Z) : Z :=
  if is_sorted_z (parse_csv l) then 1 else 0.

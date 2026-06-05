Require Import ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.

Fixpoint parse_digits (l : list Z) (acc : Z) : Z :=
  match l with
  | [] => acc
  | d :: rest => parse_digits rest (acc * 10 + d - 48)
  end.

Fixpoint split_at_comma (l : list Z) : list Z * list Z :=
  match l with
  | [] => ([], [])
  | x :: rest =>
      if Z.eqb x 44 then ([], rest)
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
  | O => []
  | S fuel' =>
      match l with
      | [] => []
      | _ =>
          let '(v, rest) := parse_one_int l in
          v :: parse_csv_aux rest fuel'
      end
  end.

Definition parse_csv (l : list Z) : list Z :=
  parse_csv_aux l (List.length l).

Fixpoint digit_chars (l : list Z) : Prop :=
  match l with
  | [] => True
  | x :: rest => 48 <= x <= 57 /\ digit_chars rest
  end.

Definition valid_token (tok : list Z) : Prop :=
  match tok with
  | [] => False
  | 45 :: ds =>
      ds <> [] /\
      digit_chars ds /\
      parse_digits ds 0 <= 2147483647
  | _ =>
      digit_chars tok /\
      parse_digits tok 0 <= 2147483647
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

Fixpoint all_valid_tokens (toks : list (list Z)) : Prop :=
  match toks with
  | [] => True
  | tok :: rest => valid_token tok /\ all_valid_tokens rest
  end.

Definition starts_with_comma (l : list Z) : Prop :=
  match l with
  | [] => False
  | x :: _ => x = 44
  end.

Fixpoint ends_with_comma (l : list Z) : Prop :=
  match l with
  | [] => False
  | x :: [] => x = 44
  | _ :: rest => ends_with_comma rest
  end.

Fixpoint no_adjacent_commas (l : list Z) : Prop :=
  match l with
  | [] => True
  | x :: rest =>
      match rest with
      | [] => True
      | y :: _ =>
          (x = 44 -> y <> 44) /\
          no_adjacent_commas rest
      end
  end.

Fixpoint token_count (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: rest =>
      (if Z.eqb x 44 then 1 else 0) + token_count rest
  end.

Definition csv_token_count (l : list Z) : Z :=
  match l with
  | [] => 0
  | _ => 1 + token_count l
  end.

Definition aug_count_ge_array_007_pre (l : list Z) : Prop :=
  match l with
  | [] => True
  | _ =>
      ~ starts_with_comma l /\
      ~ ends_with_comma l /\
      no_adjacent_commas l /\
      all_valid_tokens (split_csv_tokens l) /\
      csv_token_count l <= 64
  end.

Fixpoint count_ge_neg1 (xs : list Z) : Z :=
  match xs with
  | [] => 0
  | x :: rest =>
      (if Z.geb x (-1) then 1 else 0) + count_ge_neg1 rest
  end.

Definition aug_count_ge_array_007_spec (l : list Z) : Z :=
  count_ge_neg1 (parse_csv l).

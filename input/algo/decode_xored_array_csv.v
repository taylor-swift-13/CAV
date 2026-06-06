Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition zlength {A : Type} (l : list A) : Z :=
  Z.of_nat (List.length l).

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

Definition parse_token (tok : list Z) : Z :=
  parse_digits tok 0.

Fixpoint parse_csv_aux (l : list Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      match l with
      | [] => []
      | _ =>
          let '(tok, rest) := split_at_comma l in
          parse_token tok :: parse_csv_aux rest fuel'
      end
  end.

Definition parse_csv (l : list Z) : list Z :=
  parse_csv_aux l (List.length l).

Fixpoint digit_chars (l : list Z) : Prop :=
  match l with
  | [] => True
  | c :: rest => 48 <= c <= 57 /\ digit_chars rest
  end.

Definition valid_token (tok : list Z) : Prop :=
  tok <> [] /\
  digit_chars tok /\
  parse_digits tok 0 <= 2147483647.

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
  | c :: _ => c = 44
  end.

Fixpoint ends_with_comma (l : list Z) : Prop :=
  match l with
  | [] => False
  | [c] => c = 44
  | _ :: rest => ends_with_comma rest
  end.

Fixpoint no_adjacent_commas (l : list Z) : Prop :=
  match l with
  | [] => True
  | x :: rest =>
      match rest with
      | [] => True
      | y :: _ => (x = 44 -> y <> 44) /\ no_adjacent_commas rest
      end
  end.

Fixpoint decode_xored_values_aux (cur : Z) (encoded : list Z) : list Z :=
  match encoded with
  | [] => []
  | v :: rest =>
      let next := Z.lxor cur v in
      next :: decode_xored_values_aux next rest
  end.

Definition decode_xored_values (first : Z) (encoded : list Z) : list Z :=
  first :: decode_xored_values_aux first encoded.

Fixpoint digits_rev_aux (n : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      if Z.leb n 9 then [48 + n]
      else (48 + Z.rem n 10) :: digits_rev_aux (Z.div n 10) fuel'
  end.

Definition digits_of_nonneg (n : Z) : list Z :=
  rev (digits_rev_aux n 10).

Fixpoint encode_csv_values (vals : list Z) : list Z :=
  match vals with
  | [] => []
  | [x] => digits_of_nonneg x
  | x :: rest => digits_of_nonneg x ++ 44 :: encode_csv_values rest
  end.

Definition decode_xored_array_csv_spec (l : list Z) (first : Z) : list Z :=
  encode_csv_values (decode_xored_values first (parse_csv l)).

Definition decode_xored_array_csv_pre (l : list Z) (first out_cap : Z) : Prop :=
  0 <= first /\
  first <= 2147483647 /\
  0 <= out_cap /\
  match l with
  | [] =>
      zlength (decode_xored_array_csv_spec l first) + 1 <= out_cap
  | _ =>
      ~ starts_with_comma l /\
      ~ ends_with_comma l /\
      no_adjacent_commas l /\
      all_valid_tokens (split_csv_tokens l) /\
      zlength (decode_xored_array_csv_spec l first) + 1 <= out_cap
  end
.

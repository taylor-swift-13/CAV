Require Import ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.

Definition is_digit (c : Z) : bool :=
  andb (48 <=? c) (c <=? 57).

Fixpoint parse_digits (l : list Z) (acc : Z) : Z :=
  match l with
  | [] => acc
  | d :: rest => parse_digits rest (acc * 10 + d - 48)
  end.

Fixpoint span_digits (l : list Z) : list Z * list Z :=
  match l with
  | [] => ([], [])
  | c :: rest =>
      if is_digit c then
        let '(ds, suf) := span_digits rest in
        (c :: ds, suf)
      else
        ([], c :: rest)
  end.

Definition drop_comma (l : list Z) : list Z :=
  match l with
  | 44 :: rest => rest
  | _ => l
  end.

Fixpoint parse_stream_aux (l : list Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      match l with
      | [] => []
      | 45 :: rest =>
          let '(ds, suf) := span_digits rest in
          (- parse_digits ds 0) :: parse_stream_aux (drop_comma suf) fuel'
      | 44 :: rest =>
          0 :: parse_stream_aux rest fuel'
      | c :: rest =>
          if is_digit c then
            let '(ds, suf) := span_digits rest in
            parse_digits (c :: ds) 0 :: parse_stream_aux (drop_comma suf) fuel'
          else
            []
      end
  end.

Definition parse_stream (l : list Z) : list Z :=
  parse_stream_aux l (List.length l).

Fixpoint all_multiples_of_5 (xs : list Z) : Z :=
  match xs with
  | [] => 1
  | x :: rest =>
      if Z.eqb (Z.rem x 5) 0 then all_multiples_of_5 rest else 0
  end.

Fixpoint stream_safe_aux (l : list Z) (fuel : nat) : Prop :=
  match fuel with
  | O => l = []
  | S fuel' =>
      match l with
      | [] => True
      | 45 :: rest =>
          let '(ds, suf) := span_digits rest in
          parse_digits ds 0 <= 2147483647 /\
          stream_safe_aux (drop_comma suf) fuel'
      | 44 :: rest =>
          stream_safe_aux rest fuel'
      | c :: rest =>
          48 <= c <= 57 /\
          let '(ds, suf) := span_digits rest in
          parse_digits (c :: ds) 0 <= 2147483647 /\
          stream_safe_aux (drop_comma suf) fuel'
      end
  end.

Definition aug_all_multiple_stream_003_pre (l : list Z) : Prop :=
  stream_safe_aux l (List.length l).

Definition aug_all_multiple_stream_003_spec (l : list Z) : Z :=
  all_multiples_of_5 (parse_stream l).

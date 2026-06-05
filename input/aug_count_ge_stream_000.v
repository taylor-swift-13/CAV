Require Import ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.

Definition is_digit (x : Z) : bool :=
  Z.leb 48 x && Z.leb x 57.

Definition is_allowed_char (x : Z) : Prop :=
  x = 45 \/ x = 44 \/ (48 <= x <= 57).

Fixpoint parse_digits_prefix (l : list Z) (acc : Z) : Z * list Z :=
  match l with
  | [] => (acc, [])
  | x :: rest =>
      if is_digit x
      then parse_digits_prefix rest (acc * 10 + x - 48)
      else (acc, l)
  end.

Definition digit_prefix_value (l : list Z) : Z :=
  fst (parse_digits_prefix l 0).

Definition skip_comma (l : list Z) : list Z :=
  match l with
  | 44 :: rest => rest
  | _ => l
  end.

Definition parse_one (l : list Z) : Z * list Z :=
  match l with
  | [] => (0, [])
  | 45 :: rest =>
      let '(v, rest1) := parse_digits_prefix rest 0 in
      (- v, skip_comma rest1)
  | _ =>
      let '(v, rest1) := parse_digits_prefix l 0 in
      (v, skip_comma rest1)
  end.

Fixpoint parse_all_aux (l : list Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      match l with
      | [] => []
      | _ =>
          let '(v, rest) := parse_one l in
          v :: parse_all_aux rest fuel'
      end
  end.

Definition parse_all (l : list Z) : list Z :=
  parse_all_aux l (List.length l).

Fixpoint iteration_count_aux (l : list Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      match l with
      | [] => 0
      | _ =>
          let '(_, rest) := parse_one l in
          1 + iteration_count_aux rest fuel'
      end
  end.

Definition iteration_count (l : list Z) : Z :=
  iteration_count_aux l (List.length l).

Fixpoint all_allowed_chars (l : list Z) : Prop :=
  match l with
  | [] => True
  | x :: rest => is_allowed_char x /\ all_allowed_chars rest
  end.

Fixpoint all_parse_prefixes_bounded (l : list Z) : Prop :=
  match l with
  | [] => True
  | x :: rest =>
      ((48 <= x <= 57) -> digit_prefix_value l <= 2147483647) /\
      (x = 45 -> digit_prefix_value rest <= 2147483647) /\
      all_parse_prefixes_bounded rest
  end.

Definition aug_count_ge_stream_000_pre (l : list Z) : Prop :=
  all_allowed_chars l /\
  all_parse_prefixes_bounded l.

Fixpoint count_ge_neg8 (xs : list Z) : Z :=
  match xs with
  | [] => 0
  | x :: rest =>
      (if Z.geb x (-8) then 1 else 0) + count_ge_neg8 rest
  end.

Definition aug_count_ge_stream_000_spec (l : list Z) : Z :=
  count_ge_neg8 (parse_all l).

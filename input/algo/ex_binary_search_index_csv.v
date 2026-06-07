Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition zlength {A : Type} (l : list A) : Z :=
  Z.of_nat (List.length l).

Definition is_digitb (c : Z) : bool :=
  Z.leb 48 c && Z.leb c 57.

Definition is_digit (c : Z) : Prop :=
  48 <= c <= 57.

Definition allowed_char (c : Z) : Prop :=
  c = 44 \/ c = 45 \/ is_digit c.

Fixpoint parse_digits (l : list Z) (acc : Z) : Z * list Z :=
  match l with
  | [] => (acc, [])
  | c :: rest =>
      if is_digitb c then
        parse_digits rest (acc * 10 + c - 48)
      else
        (acc, l)
  end.

Definition drop_optional_comma (l : list Z) : list Z :=
  match l with
  | 44 :: rest => rest
  | _ => l
  end.

Definition parse_step (l : list Z) : Z * list Z :=
  match l with
  | [] => (0, [])
  | 45 :: rest =>
      let '(v, rest1) := parse_digits rest 0 in
      (- v, drop_optional_comma rest1)
  | _ =>
      let '(v, rest1) := parse_digits l 0 in
      (v, drop_optional_comma rest1)
  end.

Fixpoint parse_csv_aux (l : list Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      match l with
      | [] => []
      | _ =>
          let '(v, rest) := parse_step l in
          v :: parse_csv_aux rest fuel'
      end
  end.

Definition parse_csv (l : list Z) : list Z :=
  parse_csv_aux l (List.length l).

Fixpoint digit_run_safe (l : list Z) (acc : Z) : Prop :=
  match l with
  | [] => True
  | c :: rest =>
      if is_digitb c then
        acc * 10 + c <= 2147483647 /\
        digit_run_safe rest (acc * 10 + c - 48)
      else
        True
  end.

Definition step_safe (l : list Z) : Prop :=
  match l with
  | [] => True
  | c :: rest =>
      allowed_char c /\
      match c with
      | 45 => digit_run_safe rest 0
      | _ => digit_run_safe l 0
      end
  end.

Fixpoint parser_safe_aux (l : list Z) (fuel : nat) : Prop :=
  match fuel with
  | O => l = []
  | S fuel' =>
      match l with
      | [] => True
      | _ => step_safe l /\ parser_safe_aux (snd (parse_step l)) fuel'
      end
  end.

Definition parser_safe (l : list Z) : Prop :=
  parser_safe_aux l (List.length l).

Fixpoint sorted_nondecreasing (xs : list Z) : Prop :=
  match xs with
  | [] => True
  | x :: rest =>
      match rest with
      | [] => True
      | y :: _ => x <= y /\ sorted_nondecreasing rest
      end
  end.

Definition binary_search_index_spec_values (xs : list Z) (target r : Z) : Prop :=
  (r = -1 /\ ~ In target xs) \/
  (exists prefix suffix,
     xs = prefix ++ target :: suffix /\
     r = zlength prefix).

Definition ex_binary_search_index_csv_pre (l : list Z) : Prop :=
  parser_safe l /\
  zlength (parse_csv l) <= 128 /\
  sorted_nondecreasing (parse_csv l).

Definition ex_binary_search_index_csv_spec (l : list Z) (target r : Z) : Prop :=
  binary_search_index_spec_values (parse_csv l) target r.

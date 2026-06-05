Require Import ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.

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
        -2147483648 <= acc * 10 + c - 48 /\
        acc * 10 + c - 48 <= 2147483647 /\
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

Definition aug_last_le_array_006_pre (l : list Z) : Prop :=
  parser_safe l /\
  Z.of_nat (List.length (parse_csv l)) <= 64.

Fixpoint last_le_1_aux (xs : list Z) (idx : Z) : Z :=
  match xs with
  | [] => -1
  | x :: rest =>
      let rest_ans := last_le_1_aux rest (idx + 1) in
      if Z.eqb rest_ans (-1) then
        if Z.leb x 1 then idx else -1
      else
        rest_ans
  end.

Definition last_le_1 (xs : list Z) : Z :=
  last_le_1_aux xs 0.

Definition aug_last_le_array_006_spec (l : list Z) : Z :=
  last_le_1 (parse_csv l).

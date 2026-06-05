Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition is_digitb (c : Z) : bool :=
  Z.leb 48 c && Z.leb c 57.

Definition is_digit (c : Z) : Prop :=
  48 <= c <= 57.

Definition allowed_char (c : Z) : Prop :=
  c = 44 \/ c = 45 \/ c = 59 \/ is_digit c.

Fixpoint parse_digits (l : list Z) (acc : Z) : Z * list Z :=
  match l with
  | [] => (acc, [])
  | c :: rest =>
      if is_digitb c then
        parse_digits rest (acc * 10 + c - 48)
      else
        (acc, l)
  end.

Definition after_sign (l : list Z) : list Z :=
  match l with
  | 45 :: rest => rest
  | _ => l
  end.

Definition parse_signed_prefix (l : list Z) : Z * list Z :=
  match l with
  | 45 :: rest =>
      let '(v, rest1) := parse_digits rest 0 in
      (- v, rest1)
  | _ => parse_digits l 0
  end.

Definition consume_separator (l : list Z) : list Z :=
  match l with
  | 59 :: rest => rest
  | 44 :: rest => rest
  | _ => l
  end.

Definition ends_row (l : list Z) : bool :=
  match l with
  | 59 :: _ => true
  | _ => false
  end.

Definition step_value (l : list Z) : Z :=
  fst (parse_signed_prefix l).

Definition step_after_number (l : list Z) : list Z :=
  snd (parse_signed_prefix l).

Definition step_rest (l : list Z) : list Z :=
  consume_separator (step_after_number l).

Definition step_ends_row (l : list Z) : bool :=
  ends_row (step_after_number l).

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
      | _ => step_safe l /\ parser_safe_aux (step_rest l) fuel'
      end
  end.

Fixpoint row_sum_safe_aux (l : list Z) (fuel : nat) (current target acc : Z) : Prop :=
  match fuel with
  | O => l = []
  | S fuel' =>
      match l with
      | [] => True
      | _ =>
          let add :=
            if Z.eqb current target then step_value l else 0 in
          let acc' := acc + add in
          -2147483648 <= acc' <= 2147483647 /\
          row_sum_safe_aux
            (step_rest l)
            fuel'
            (if step_ends_row l then current + 1 else current)
            target
            acc'
      end
  end.

Fixpoint ex_matrix_row_sum_aux (l : list Z) (fuel : nat) (current target : Z) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      match l with
      | [] => 0
      | _ =>
          let add :=
            if Z.eqb current target then step_value l else 0 in
          add +
          ex_matrix_row_sum_aux
            (step_rest l)
            fuel'
            (if step_ends_row l then current + 1 else current)
            target
      end
  end.

Definition ex_matrix_row_sum_pre (l : list Z) (row : Z) : Prop :=
  parser_safe_aux l (List.length l) /\
  row_sum_safe_aux l (List.length l) 1 row 0 /\
  Z.of_nat (List.length l) <= 2147483646.

Definition ex_matrix_row_sum_spec (l : list Z) (row : Z) : Z :=
  ex_matrix_row_sum_aux l (List.length l) 1 row.

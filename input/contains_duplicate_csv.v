Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint parse_digits (l : list Z) (acc : Z) : Z :=
  match l with
  | [] => acc
  | c :: rest => parse_digits rest (acc * 10 + (c - 48))
  end.

Definition allowed_char (c : Z) : Prop :=
  c = 44 \/ c = 45 \/ (48 <= c /\ c <= 57).

Fixpoint allowed_chars (l : list Z) : Prop :=
  match l with
  | [] => True
  | c :: rest => allowed_char c /\ allowed_chars rest
  end.

Fixpoint take_digits (l : list Z) : list Z * list Z :=
  match l with
  | [] => ([], [])
  | c :: rest =>
      if Z.leb 48 c then
        if Z.leb c 57 then
          let '(ds, after) := take_digits rest in
          (c :: ds, after)
        else ([], l)
      else ([], l)
  end.

Definition drop_comma (l : list Z) : list Z :=
  match l with
  | 44 :: rest => rest
  | _ => l
  end.

Definition after_sign (l : list Z) : list Z :=
  match l with
  | 45 :: rest => rest
  | _ => l
  end.

Definition step_digits_value (l : list Z) : Z :=
  let '(ds, _) := take_digits (after_sign l) in
  parse_digits ds 0.

Definition step_value (l : list Z) : Z :=
  match l with
  | 45 :: _ => - step_digits_value l
  | _ => step_digits_value l
  end.

Definition step_rest (l : list Z) : list Z :=
  let '(_, rest) := take_digits (after_sign l) in
  drop_comma rest.

Fixpoint parse_csv_aux (l : list Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      match l with
      | [] => []
      | _ => step_value l :: parse_csv_aux (step_rest l) fuel'
      end
  end.

Fixpoint parser_safe_aux (l : list Z) (fuel : nat) : Prop :=
  match l with
  | [] => True
  | _ =>
      match fuel with
      | O => False
      | S fuel' =>
          step_digits_value l <= 2147483647 /\
          parser_safe_aux (step_rest l) fuel'
      end
  end.

Definition parse_csv (l : list Z) : list Z :=
  parse_csv_aux l (List.length l).

Fixpoint mem_z (x : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | y :: rest => if Z.eqb x y then true else mem_z x rest
  end.

Fixpoint has_duplicate_z (l : list Z) : bool :=
  match l with
  | [] => false
  | x :: rest => if mem_z x rest then true else has_duplicate_z rest
  end.

Definition contains_duplicate_csv_pre (l : list Z) : Prop :=
  allowed_chars l /\
  parser_safe_aux l (List.length l) /\
  Z.of_nat (List.length (parse_csv l)) <= 64 /\
  Z.of_nat (List.length l) <= 2147483647.

Definition contains_duplicate_csv_spec (l : list Z) : Z :=
  if has_duplicate_z (parse_csv l) then 1 else 0.

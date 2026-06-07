Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition zlength {A : Type} (l : list A) : Z :=
  Z.of_nat (List.length l).

Definition is_digitb (c : Z) : bool :=
  if Z.leb 48 c then Z.leb c 57 else false.

Definition consume_sign (l : list Z) : Z * list Z :=
  match l with
  | 45 :: rest => (-1, rest)
  | _ => (1, l)
  end.

Fixpoint consume_digits (l : list Z) (acc : Z) : list Z * Z :=
  match l with
  | [] => ([], acc)
  | c :: rest =>
      if is_digitb c
      then consume_digits rest (acc * 10 + c - 48)
      else (l, acc)
  end.

Definition consume_comma (l : list Z) : list Z :=
  match l with
  | 44 :: rest => rest
  | _ => l
  end.

Fixpoint digits_safe_from (l : list Z) (acc : Z) : Prop :=
  match l with
  | [] => True
  | c :: rest =>
      if is_digitb c
      then acc * 10 + c <= 2147483647 /\
           digits_safe_from rest (acc * 10 + c - 48)
      else True
  end.

Fixpoint parse_csv_aux (l : list Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      match l with
      | [] => []
      | _ =>
          let '(sign, rest1) := consume_sign l in
          let '(rest2, value) := consume_digits rest1 0 in
          (sign * value) :: parse_csv_aux (consume_comma rest2) fuel'
      end
  end.

Definition parse_csv_impl (l : list Z) : list Z :=
  parse_csv_aux l (List.length l).

Fixpoint parser_safe_aux (l : list Z) (fuel : nat) : Prop :=
  match fuel with
  | O => l = []
  | S fuel' =>
      match l with
      | [] => True
      | _ =>
          let rest1 := snd (consume_sign l) in
          let rest2 := fst (consume_digits rest1 0) in
          digits_safe_from rest1 0 /\
          parser_safe_aux (consume_comma rest2) fuel'
      end
  end.

Definition parser_safe (l : list Z) : Prop :=
  parser_safe_aux l (List.length l).

Fixpoint count_occ_z (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | y :: rest => (if Z.eqb x y then 1 else 0) + count_occ_z x rest
  end.

Fixpoint count_good_pairs_vals (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: rest => count_occ_z x rest + count_good_pairs_vals rest
  end.

Definition count_good_pairs_csv_pre (l : list Z) : Prop :=
  parser_safe l /\
  zlength (parse_csv_impl l) <= 128.

Definition count_good_pairs_csv_spec (l : list Z) : Z :=
  count_good_pairs_vals (parse_csv_impl l).

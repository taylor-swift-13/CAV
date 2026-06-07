Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition zlength {A : Type} (l : list A) : Z :=
  Z.of_nat (List.length l).

Definition is_digitb (c : Z) : bool :=
  Z.leb 48 c && Z.leb c 57.

Definition is_spaceb (c : Z) : bool :=
  Z.eqb c 32.

Fixpoint ascii_nonzero (l : list Z) : Prop :=
  match l with
  | [] => True
  | x :: xs => 1 <= x <= 127 /\ ascii_nonzero xs
  end.

Fixpoint count_nonspace (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if is_spaceb x then 0 else 1) + count_nonspace xs
  end.

Fixpoint digits_only (l : list Z) : option (list Z) :=
  match l with
  | [] => Some []
  | x :: xs =>
      if is_spaceb x then
        digits_only xs
      else if is_digitb x then
        match digits_only xs with
        | Some ds => Some ((x - 48) :: ds)
        | None => None
        end
      else
        None
  end.

Definition luhn_double (d : Z) : Z :=
  let v := 2 * d in
  if Z.leb 10 v then v - 9 else v.

Fixpoint luhn_sum_rev (rev_digits : list Z) (dbl : bool) : Z :=
  match rev_digits with
  | [] => 0
  | d :: ds =>
      (if dbl then luhn_double d else d) + luhn_sum_rev ds (negb dbl)
  end.

Definition ex_luhn_valid_ascii_pre (l : list Z) : Prop :=
  ascii_nonzero l /\ count_nonspace l <= 128.

Definition ex_luhn_valid_ascii_spec (l : list Z) : Z :=
  match digits_only l with
  | None => 0
  | Some ds =>
      if Z.leb 2 (zlength ds) then
        if Z.eqb (Z.rem (luhn_sum_rev (rev ds) false) 10) 0 then 1 else 0
      else 0
  end.

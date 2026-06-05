Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.
Import ListNotations.

Definition digit_to_Z (d : Z) : Z :=
  if Z.eq_dec d 49 then 1 else 0.

Definition Z_to_digit (z : Z) : Z :=
  if Z.eq_dec z 0 then 48 else 49.

Fixpoint is_bin_chars (l : list Z) : Prop :=
  match l with
  | [] => True
  | d :: rest => (d = 48 \/ d = 49) /\ is_bin_chars rest
  end.

Fixpoint rev_bin_add_carry_fuel (fuel : nat) (ra rb : list Z) (carry : Z) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      match ra, rb with
      | [], [] =>
          if Z.eq_dec carry 0 then [] else [49]
      | a :: ra', [] =>
          let sum := digit_to_Z a + carry in
          Z_to_digit (Z.modulo sum 2) :: rev_bin_add_carry_fuel fuel' ra' [] (Z.div sum 2)
      | [], b :: rb' =>
          let sum := digit_to_Z b + carry in
          Z_to_digit (Z.modulo sum 2) :: rev_bin_add_carry_fuel fuel' [] rb' (Z.div sum 2)
      | a :: ra', b :: rb' =>
          let sum := digit_to_Z a + digit_to_Z b + carry in
          Z_to_digit (Z.modulo sum 2) :: rev_bin_add_carry_fuel fuel' ra' rb' (Z.div sum 2)
      end
  end.

Fixpoint strip_leading_zeroes (l : list Z) : list Z :=
  match l with
  | [] => []
  | 48 :: rest =>
      match strip_leading_zeroes rest with
      | [] => []
      | trimmed => trimmed
      end
  | _ => l
  end.

Definition normalize_bin_chars (l : list Z) : list Z :=
  match strip_leading_zeroes l with
  | [] => [48]
  | trimmed => trimmed
  end.

Definition add_binary_strings_spec (a b : list Z) : list Z :=
  normalize_bin_chars
    (rev (rev_bin_add_carry_fuel (length a + length b + 1)%nat (rev a) (rev b) 0)).

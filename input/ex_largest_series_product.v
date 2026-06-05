Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint product (l : list Z) : Z :=
  match l with
  | [] => 1
  | x :: xs => x * product xs
  end.

Definition zlength {A : Type} (l : list A) : Z :=
  Z.of_nat (length l).

Definition digit_value (c : Z) : Z :=
  c - 48.

Definition slice (l : list Z) (start len : Z) : list Z :=
  firstn (Z.to_nat len) (skipn (Z.to_nat start) l).

Definition window_product (l : list Z) (start len : Z) : Z :=
  product (map digit_value (slice l start len)).

Fixpoint largest_series_product_aux (l : list Z) (span : Z) (fuel : nat) : Z :=
  match fuel with
  | O => window_product l 0 span
  | S fuel' =>
      match l with
      | [] => window_product l 0 span
      | _ :: xs =>
          Z.max (window_product l 0 span)
                (largest_series_product_aux xs span fuel')
      end
  end.

Definition ex_largest_series_product_spec (l : list Z) (span : Z) : Z :=
  if Z.eqb span 0 then
    1
  else
    largest_series_product_aux l span (Z.to_nat (zlength l - span)).

Definition ex_largest_series_product_pre (l : list Z) (span : Z) : Prop :=
  0 <= span /\
  span <= zlength l /\
  zlength l + span <= 2147483647 /\
  Forall (fun c => 48 <= c <= 57) l /\
  (forall i k : Z,
      0 <= i /\
      0 <= k /\
      k <= span /\
      i + k <= zlength l ->
      -2147483648 <= window_product l i k <= 2147483647).

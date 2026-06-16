Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition ascii_of (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of c) (string_of_list rest)
  end.

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: list_ascii_of_string rest
  end.

Definition char_list_string (l : list Z) (s : string) : Prop :=
  s = string_of_list l.

Definition bool_of (z : Z) : bool :=
  Z.eqb z 1.

Definition nat_of (z : Z) : nat :=
  Z.to_nat z.

Definition ascii_range (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0 < 256.

Definition ascii_range_7bit (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0 <= 127.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Definition ascii_letter_index (c : Z) : Z :=
  let lower :=
      if Z.leb 65 c then
        if Z.leb c 90 then c - 65 + 97 else c
      else c in
  if Z.leb 97 lower then
    if Z.leb lower 122 then lower - 97 else -1
  else -1.

Fixpoint has_letter_index (l : list Z) (k : Z) : bool :=
  match l with
  | nil => false
  | c :: rest =>
      if Z.eqb (ascii_letter_index c) k then true else has_letter_index rest k
  end.

Fixpoint all_letters_upto (l : list Z) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
      if has_letter_index l (Z.of_nat fuel') then
        all_letters_upto l fuel'
      else
        false
  end.

Definition ex_pangram_ascii_spec (l : list Z) : Z :=
  if all_letters_upto l 26%nat then 1 else 0.

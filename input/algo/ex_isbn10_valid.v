Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint ex_isbn10_valid_scan (l : list Z) (pos sum : Z) : Z :=
  match l with
  | nil =>
      if Z.eqb pos 10 then
        if Z.eqb (Z.rem sum 11) 0 then 1 else 0
      else 0
  | c :: rest =>
      if Z.eqb c 45 then
        ex_isbn10_valid_scan rest pos sum
      else if Z.eqb c 88 then
        if Z.eqb pos 9 then
          ex_isbn10_valid_scan rest (pos + 1) (sum + 10 * (10 - pos))
        else 0
      else if Z.leb 48 c then
        if Z.leb c 57 then
          if Z.leb 10 pos then
            0
          else
            ex_isbn10_valid_scan rest (pos + 1) (sum + (c - 48) * (10 - pos))
        else 0
      else 0
  end.

Definition ex_isbn10_valid_spec (l : list Z) : Z :=
  ex_isbn10_valid_scan l 0 0.

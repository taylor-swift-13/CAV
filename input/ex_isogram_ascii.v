Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint z_mem (x : Z) (seen : list Z) : bool :=
  match seen with
  | nil => false
  | y :: ys => if Z.eqb x y then true else z_mem x ys
  end.

Definition ascii_letter_index (c : Z) : Z :=
  let lower :=
      if Z.leb 65 c then
        if Z.leb c 90 then c - 65 + 97 else c
      else c in
  if Z.leb 97 lower then
    if Z.leb lower 122 then lower - 97 else -1
  else -1.

Fixpoint ex_isogram_ascii_scan (l seen : list Z) : Z :=
  match l with
  | nil => 1
  | c :: rest =>
      let k := ascii_letter_index c in
      if Z.eqb k (-1) then
        ex_isogram_ascii_scan rest seen
      else if z_mem k seen then
        0
      else
        ex_isogram_ascii_scan rest (k :: seen)
  end.

Definition ex_isogram_ascii_spec (l : list Z) : Z :=
  ex_isogram_ascii_scan l nil.

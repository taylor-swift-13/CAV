Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Definition ex_protein_is_stop_codon (a b c : Z) : bool :=
  if Z.eq_dec a 85 then
    if Z.eq_dec b 65 then
      if Z.eq_dec c 65 then true
      else if Z.eq_dec c 71 then true else false
    else if Z.eq_dec b 71 then
      if Z.eq_dec c 65 then true else false
    else false
  else false.

Fixpoint ex_protein_stop_index_spec (l : list Z) : Z :=
  match l with
  | a :: b :: c :: xs =>
      if ex_protein_is_stop_codon a b c then
        0
      else
        1 + ex_protein_stop_index_spec xs
  | _ => 0
  end.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition is_open_bracket (c : Z) : bool :=
  Z.eqb c 40 || Z.eqb c 91 || Z.eqb c 123.

Definition is_close_bracket (c : Z) : bool :=
  Z.eqb c 41 || Z.eqb c 93 || Z.eqb c 125.

Definition bracket_matches (open close : Z) : bool :=
  (Z.eqb open 40 && Z.eqb close 41) ||
  (Z.eqb open 91 && Z.eqb close 93) ||
  (Z.eqb open 123 && Z.eqb close 125).

Fixpoint ex_matching_brackets_ascii_go (st l : list Z) : Z :=
  match l with
  | [] =>
      match st with
      | [] => 1
      | _ => 0
      end
  | c :: rest =>
      if is_open_bracket c then
        ex_matching_brackets_ascii_go (c :: st) rest
      else if is_close_bracket c then
        match st with
        | [] => 0
        | open :: st' =>
            if bracket_matches open c then
              ex_matching_brackets_ascii_go st' rest
            else 0
        end
      else
        ex_matching_brackets_ascii_go st rest
  end.

Definition ex_matching_brackets_ascii_spec (l : list Z) : Z :=
  ex_matching_brackets_ascii_go [] l.

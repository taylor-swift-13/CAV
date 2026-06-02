Require Import ZArith.
Require Import List.

Open Scope Z_scope.

Fixpoint bin_val_aux (l : list Z) (acc : Z) : Z :=
  match l with
  | nil => acc
  | d :: rest => bin_val_aux rest (acc * 2 + (d - 48))
  end.

Definition bin_val (l : list Z) : Z := bin_val_aux l 0.

Fixpoint is_bin_list (l : list Z) : Prop :=
  match l with
  | nil => True
  | d :: rest => (d = 48 \/ d = 49) /\ is_bin_list rest
  end.

Definition is_canonical (l : list Z) : Prop :=
  match l with
  | nil => False
  | d :: rest => d = 49 \/ rest = nil
  end.

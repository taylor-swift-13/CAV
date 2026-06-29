Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Fixpoint intersperse_list (input : list Z) (d : Z) : list Z :=
  match input with
  | nil => nil
  | x :: nil => x :: nil
  | x :: xs => x :: d :: intersperse_list xs d
  end.

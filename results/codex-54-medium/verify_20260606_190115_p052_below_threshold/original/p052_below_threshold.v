(* spec/52 *)
(* def below_threshold(l: list, t: int):
"""Return True if all numbers in the list l are below threshold t.
>>> below_threshold([1, 2, 4, 10], 100)
True
>>> below_threshold([1, 20, 4, 10], 5)
False
""" *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list Z) : Prop := True.

(* index-based (verification-friendly): all elements < t, by Znth over [0, Zlength) *)
Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall i, 0 <= i < Zlength l -> Znth i l 0 < t) <-> (output = true).

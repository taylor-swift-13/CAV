(* spec/61 *)
(*def correct_bracketing(brackets: str):
""" brackets is a string of "(" and ")".
return True if every opening bracket has a corresponding closing bracket.

>>> correct_bracketing("(")
False
>>> correct_bracketing("()")
True
>>> correct_bracketing("(()())")
True
>>> correct_bracketing(")(()")
False
""" *)

Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.

Local Open Scope Z_scope.

Definition problem_61_pre (brackets : list Z) : Prop :=
  Forall (fun c => c = 40 \/ c = 41) brackets.

Definition bool_of (z : Z) : bool :=
  Z.eqb z 1.

Definition paren_delta (x : Z) : Z :=
  if Z.eqb x 40 then 1 else if Z.eqb x 41 then -1 else 0.

Fixpoint paren_level_upto_nat (n : nat) (l : list Z) : Z :=
  match n with
  | O => 0
  | S n' => paren_level_upto_nat n' l + paren_delta (Znth (Z.of_nat n') l 0)
  end.

Definition paren_level_upto (i : Z) (l : list Z) : Z :=
  paren_level_upto_nat (Z.to_nat i) l.

Definition paren_nonnegative_prefix (i : Z) (l : list Z) : Prop :=
  forall k, 0 <= k < i -> 0 <= paren_level_upto (k + 1) l.

Definition paren_balanced (l : list Z) : Prop :=
  paren_level_upto (Zlength l) l = 0 /\
  paren_nonnegative_prefix (Zlength l) l.

Definition problem_61_spec (brackets : list Z) (output : Z) : Prop :=
  bool_of output = true <-> paren_balanced brackets.

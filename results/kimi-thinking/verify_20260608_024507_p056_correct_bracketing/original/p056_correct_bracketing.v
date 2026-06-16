(* spec/56 *)
(* def correct_bracketing(brackets: str):
 brackets is a string of "<" and ">".
return True if every opening bracket has a corresponding closing bracket.

>>> correct_bracketing("<")
False
>>> correct_bracketing("<>")
True
>>> correct_bracketing("<<><>>")
True
>>> correct_bracketing("><<>")
False
*)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Import ListNotations.

Local Open Scope Z_scope.

Definition problem_56_pre (brackets : list Z) : Prop :=
  Forall (fun c => c = 60 \/ c = 62) brackets.

Definition bool_of (z : Z) : bool :=
  Z.eqb z 1.

Definition angle_delta (x : Z) : Z :=
  if Z.eqb x 60 then 1 else if Z.eqb x 62 then -1 else 0.

Fixpoint angle_level_upto_nat (n : nat) (l : list Z) : Z :=
  match n with
  | O => 0
  | S n' => angle_level_upto_nat n' l + angle_delta (Znth (Z.of_nat n') l 0)
  end.

Definition angle_level_upto (i : Z) (l : list Z) : Z :=
  angle_level_upto_nat (Z.to_nat i) l.

Definition angle_nonnegative_prefix (i : Z) (l : list Z) : Prop :=
  forall k, 0 <= k < i -> 0 <= angle_level_upto (k + 1) l.

Definition angle_balanced (l : list Z) : Prop :=
  angle_level_upto (Zlength l) l = 0 /\
  angle_nonnegative_prefix (Zlength l) l.

Definition problem_56_spec (brackets : list Z) (output : Z) : Prop :=
  bool_of output = true <-> angle_balanced brackets.

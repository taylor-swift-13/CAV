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
(* 引入Coq标准库，用于列表（List）和ASCII字符（Ascii）的定义 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Open Scope string_scope.

Fixpoint correct_bracketing_aux (s : string) (depth : nat) : bool :=
  match s with
  | "" => match depth with 0 => true | _ => false end
  | String c s' =>
    if (Ascii.eqb c "<"%char) then
      correct_bracketing_aux s' (S depth)
    else if (Ascii.eqb c ">"%char) then
      match depth with
      | 0 => false
      | S d => correct_bracketing_aux s' d
      end
    else
      correct_bracketing_aux s' depth
  end.

Definition correct_bracketing (s : string) : bool :=
  correct_bracketing_aux s 0.

(* Pre: no special constraints for `correct_bracketing` *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition problem_56_pre (brackets : list Z) : Prop :=
  Forall (fun c => c = "<"%char \/ c = ">"%char) (list_ascii_of_string ((string_of_list brackets))).

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
  bool_of output = correct_bracketing (string_of_list brackets).

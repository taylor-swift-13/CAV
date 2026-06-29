(* spec/136 *)
(* def largest_smallest_integers(lst):
'''
Create a function that returns a tuple (a, b), where 'a' is
the largest of negative integers, and 'b' is the smallest
of positive integers in a list.
If there is no negative or positive integers, return them as None.

Examples:
largest_smallest_integers([2, 4, 1, 3, 5, 7]) == (None, 1)
largest_smallest_integers([]) == (None, None)
largest_smallest_integers([0]) == (None, None)
''' *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

(* a 是 lst 中最大的负整数（Some z）或不存在负整数（None） *)
Definition is_largest_negative (lst : list Z) (a : option Z) : Prop :=
  match a with
  | Some z => z < 0 /\ In z lst /\ (forall x, In x lst -> x < 0 -> x <= z)
  | None   => forall x, In x lst -> ~(x < 0)
  end.

(* b 是 lst 中最小的正整数（Some z）或不存在正整数（None） *)
Definition is_smallest_positive (lst : list Z) (b : option Z) : Prop :=
  match b with
  | Some z => z > 0 /\ In z lst /\ (forall x, In x lst -> x > 0 -> z <= x)
  | None   => forall x, In x lst -> ~(x > 0)
  end.

(* 任意整数列表均可 *)

(* 最终 Spec：结果 res = (a, b) 当且仅当 a 是最大的负整数（或 None），b 是最小的正整数（或 None） *)

Require Import Coq.micromega.Lia.

From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition neg_option_of_value (x : Z) : option Z :=
  if x =? 0 then None else Some x.

Definition pos_option_of_value (x : Z) : option Z :=
  if x =? 0 then None else Some x.

Definition largest_negative_state (l : list Z) (maxneg : Z) : Prop :=
  (maxneg = 0 /\ forall x, In x l -> ~ x < 0) \/
  (maxneg < 0 /\ In maxneg l /\ forall x, In x l -> x < 0 -> x <= maxneg).

Definition smallest_positive_state (l : list Z) (minpos : Z) : Prop :=
  (minpos = 0 /\ forall x, In x l -> ~ x > 0) \/
  (minpos > 0 /\ In minpos l /\ forall x, In x l -> x > 0 -> minpos <= x).

Definition largest_smallest_prefix (i : Z) (l : list Z) (maxneg minpos : Z) : Prop :=
  0 <= i <= Zlength l /\
  largest_negative_state (sublist 0 i l) maxneg /\
  smallest_positive_state (sublist 0 i l) minpos.

Definition problem_136_pre (l : list Z) : Prop :=
  True.

Definition problem_136_spec (l out : list Z) : Prop :=
  exists maxneg minpos,
      out = maxneg :: minpos :: nil /\
      largest_smallest_prefix (Zlength l) l maxneg minpos /\
      (let (a, b) := ((neg_option_of_value maxneg, pos_option_of_value minpos)) in
    is_largest_negative l a /\ is_smallest_positive l b).

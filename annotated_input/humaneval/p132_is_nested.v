(* spec/132 *)
(* def is_nested(string):
'''
Create a function that takes a string as input which contains only square brackets.
The function should return True if and only if there is a valid subsequence of brackets
where at least one bracket in the subsequence is nested.

is_nested('[[]]') ➞ True
is_nested('[]]]]]]][[[[[]') ➞ False
is_nested('[][]') ➞ False
is_nested('[]') ➞ False
is_nested('[[][]]') ➞ True
is_nested('[[]][[') ➞ True
''' *)
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope Z_scope.

Definition bracket_char (c : Z) : Prop :=
  c = 91 \/ c = 93.

Definition bool_of (z : Z) : bool :=
  Z.eqb z 1.

Definition subseq_step (state c : Z) : Z :=
  if Z.eqb state 0 then
    if Z.eqb c 91 then 1 else 0
  else if Z.eqb state 1 then
    if Z.eqb c 91 then 2 else 1
  else if Z.eqb state 2 then
    if Z.eqb c 93 then 3 else 2
  else if Z.eqb state 3 then
    if Z.eqb c 93 then 4 else 3
  else 4.

Fixpoint subseq_state_list (state : Z) (s : list Z) : Z :=
  match s with
  | [] => state
  | c :: rest => subseq_state_list (subseq_step state c) rest
  end.

Definition subseq_state_prefix (i : Z) (s : list Z) : Z :=
  subseq_state_list 0 (firstn (Z.to_nat i) s).

Definition problem_132_pre (s : list Z) : Prop :=
  Forall bracket_char s.

Definition problem_132_spec (s : list Z) (output : Z) : Prop :=
  bool_of output = true <-> subseq_state_list 0 s = 4.

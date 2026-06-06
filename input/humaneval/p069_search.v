(* spec/69 *)
(* def search(lst):
'''
You are given a non-empty list of positive integers. Return the greatest integer that is greater than
zero, and has a frequency greater than or equal to the value of the integer itself.
The frequency of an integer is the number of times it appears in the list.
If no such a value exist, return -1.
Examples:
search([4, 1, 2, 2, 3, 1]) == 2
search([1, 2, 2, 3, 3, 3, 4, 4, 4]) == 3
search([5, 5, 4, 4, 4]) == -1 *)
Require Import ZArith.
Require Import List.
Import ListNotations.

Open Scope Z_scope.
Fixpoint count (z : Z) (lst : list Z) : nat :=
  match lst with
  | [] => 0
  | h :: t => (if Z.eqb z h then 1 else 0) + count z t
  end.

Fixpoint find_max_satisfying (lst : list Z) (candidates : list Z) (current_max : Z) : Z :=
  match candidates with
  | [] => current_max
  | h :: t =>
      if Z.of_nat (count h lst) >=? h then
        find_max_satisfying lst t (Z.max h current_max)
      else
        find_max_satisfying lst t current_max
  end.

Definition search_impl (lst : list Z) : Z :=
  match lst with
  | [] => (-1)%Z
  | _ =>
      let candidates := lst in
      let max_val := find_max_satisfying lst candidates (-1)%Z in
      if max_val =? (-1)%Z then
        (-1)%Z
      else
        max_val
  end.

Definition problem_69_pre (lst : list Z) : Prop := lst <> []%list /\ (forall x, In x lst -> (x > 0)%Z).

Definition problem_69_spec (lst : list Z) (y : Z) : Prop :=
  y = search_impl lst.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition search_int_range_69 (input : list Z) : Prop :=
  forall i, 0 <= i < Zlength input -> 0 < Znth i input 0 < INT_MAX.

Fixpoint seen_values_aux_69 (seen rest : list Z) : list Z :=
  match rest with
  | [] => seen
  | x :: xs =>
      if in_dec Z.eq_dec x seen
      then seen_values_aux_69 seen xs
      else seen_values_aux_69 (seen ++ [x]) xs
  end.

Definition seen_values_69 (l : list Z) : list Z :=
  seen_values_aux_69 [] l.

Definition zcount_69 (x : Z) (l : list Z) : Z :=
  Z.of_nat (count x l).

Definition positive_list_69 (l : list Z) : Prop :=
  forall x, In x l -> 0 < x.

Definition eligible_69 (l : list Z) (x : Z) : Prop :=
  zcount_69 x l >= x.

Definition counts_for_values_69 (vals prefix : list Z) : list Z :=
  map (fun v => zcount_69 v prefix) vals.

Definition prefix_69 (input : list Z) (i : Z) : list Z :=
  sublist 0 i input.

Definition search_prefix_69 (input : list Z) (i : Z) : Z :=
  search_impl (prefix_69 input i).

Fixpoint has_first_69 (fuel : nat) (x : Z) (vals : list Z) : bool :=
  match fuel, vals with
  | O, _ => false
  | S fuel', [] => false
  | S fuel', v :: vs =>
      if Z.eqb x v then true else has_first_69 fuel' x vs
  end.

Fixpoint update_first_count_69
  (fuel : nat) (x : Z) (vals cnts : list Z) : list Z :=
  match fuel, vals, cnts with
  | O, _, _ => cnts
  | S fuel', v :: vs, c :: cs =>
      if Z.eqb x v
      then (c + 1) :: cs
      else c :: update_first_count_69 fuel' x vs cs
  | _, _, _ => cnts
  end.

Definition max_after_seen_69 (prefix : list Z) (x max : Z) : Z :=
  if (zcount_69 x prefix + 1 >=? x) && (x >? max) then x else max.

Definition max_after_inner_69 (prefix : list Z) (j : Z) (x max : Z) (vals : list Z) : Z :=
  if has_first_69 (Z.to_nat j) x vals
  then max_after_seen_69 prefix x max
  else max.

Definition hit_max_69 (vals cnts : list Z) (j max : Z) : Z :=
  if ((Znth j cnts 0 + 1 >=? Znth j vals 0) && (Znth j vals 0 >? max))
  then Znth j vals 0
  else max.

Definition search_outer_state_69
  (input : list Z) (i : Z) (vals cnts : list Z) (max : Z) : Prop :=
  0 <= i <= Zlength input /\
  vals = seen_values_69 (prefix_69 input i) /\
  cnts = counts_for_values_69 vals (prefix_69 input i) /\
  max = search_prefix_69 input i.

Definition search_inner_state_69
  (input : list Z) (i j : Z) (vals cnts : list Z) (has max : Z) : Prop :=
  0 <= i < Zlength input /\
  let prefix := prefix_69 input i in
  let x := Znth i input 0 in
  let base_vals := seen_values_69 prefix in
  let base_cnts := counts_for_values_69 base_vals prefix in
  0 <= j <= Zlength base_vals /\
  vals = base_vals /\
  cnts = update_first_count_69 (Z.to_nat j) x base_vals base_cnts /\
  has = (if has_first_69 (Z.to_nat j) x base_vals then 1 else 0) /\
  max = max_after_inner_69 prefix j x (search_prefix_69 input i) base_vals.

Definition search_inner_to_outer_69
  (input : list Z) (i : Z) (vals cnts : list Z) (has max : Z) : Prop :=
  if Z.eqb has 1
  then search_outer_state_69 input (i + 1) vals cnts max
  else search_inner_state_69 input i (Zlength vals) vals cnts has max.

Definition search_after_val_write_69
  (input : list Z) (i : Z) (vals cnts : list Z) (max x freq_size : Z) : Prop :=
  exists base_vals base_cnts,
    x = Znth i input 0 /\
    freq_size = Zlength base_vals /\
    vals = base_vals ++ [x] /\
    cnts = base_cnts /\
    search_inner_to_outer_69 input i base_vals base_cnts 0 max.

Definition search_outer_add_new_69
  (input : list Z) (i : Z) (vals cnts : list Z) (max x freq_size added : Z) : Prop :=
  x = Znth i input 0 /\
  added = 1 /\
  freq_size = Zlength vals /\
  search_outer_state_69 input (i + 1) vals cnts max.

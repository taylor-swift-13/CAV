(* spec/70 *)
(* def strange_sort_list(lst):
'''
Given list of integers, return list in strange order.
Strange sorting, is when you start with the minimum value,
then maximum of the remaining integers, then minimum and so on.

Examples:
strange_sort_list([1, 2, 3, 4]) == [1, 4, 2, 3]
strange_sort_list([5, 5, 5, 5]) == [5, 5, 5, 5]
strange_sort_list([]) == []
''' *)
(* 引入 Coq 标准库以使用列表、自然数和置换等概念 *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.

(* 引入列表的标准表示法，如 [] 和 x :: xs *)
Import ListNotations.
Open Scope Z_scope.

Fixpoint remove_one (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => if Z.eqb x h then t else h :: remove_one x t
  end.

Fixpoint list_min (l : list Z) : option Z :=
  match l with
  | [] => None
  | h :: t =>
    match list_min t with
    | None => Some h
    | Some m => Some (Z.min h m)
    end
  end.

Fixpoint list_max (l : list Z) : option Z :=
  match l with
  | [] => None
  | h :: t =>
    match list_max t with
    | None => Some h
    | Some m => Some (Z.max h m)
    end
  end.

Fixpoint strange_sort_aux (l : list Z) (fuel : nat) (is_min : bool) : list Z :=
  match fuel with
  | 0%nat => []
  | S n =>
    match l with
    | [] => []
    | _ =>
      match if is_min then list_min l else list_max l with
      | None => []
      | Some v => v :: strange_sort_aux (remove_one v l) n (negb is_min)
      end
    end
  end.

Definition strange_sort_list (l : list Z) : list Z :=
  strange_sort_aux l (length l) true.



Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition problem_70_pre (l : list Z) : Prop :=
  True.

Definition problem_70_spec (input output : list Z) : Prop :=
  (output = strange_sort_list input).

Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
  if Z.eqb ascending 0 then True else Sorted Z.le l.

Fixpoint copy_prefix_nat (n : nat) (input : list Z) : list Z :=
  match n with
  | O => []
  | S n' => copy_prefix_nat n' input ++ [Znth (Z.of_nat n') input 0]
  end.

Definition copy_prefix (n : Z) (input : list Z) : list Z :=
  copy_prefix_nat (Z.to_nat n) input.

Definition strange_index (size i : Z) : Z :=
  if Z.eqb (Z.rem i 2) 0
  then i ÷ 2
  else size - 1 - (i ÷ 2).

Fixpoint strange_output_prefix_nat (size : Z) (n : nat) (sorted_l : list Z) : list Z :=
  match n with
  | O => []
  | S n' =>
      strange_output_prefix_nat size n' sorted_l ++
      [Znth (strange_index size (Z.of_nat n')) sorted_l 0]
  end.

Definition strange_output_prefix (size i : Z) (sorted_l : list Z) : list Z :=
  strange_output_prefix_nat size (Z.to_nat i) sorted_l.

Definition strange_output (size : Z) (sorted_l : list Z) : list Z :=
  strange_output_prefix size size sorted_l.


(* Ground-truth proof helpers. *)

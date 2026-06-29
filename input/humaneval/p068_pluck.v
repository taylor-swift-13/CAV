(* spec/68 *)
(* def pluck(arr):
Given an array representing a branch of a tree that has non-negative integer nodes
your task is to pluck one of the nodes and return it.
The plucked node should be the node with the smallest even value.
If multiple nodes with the same smallest even value are found return the node that has smallest index.

The plucked node should be returned in a list, [ smalest_value, its index ],
If there are no even values or the given array is empty, return [].

Example 1:
Input: [4,2,3]
Output: [2, 1]
Explanation: 2 has the smallest even value, and 2 has the smallest index.

Example 2:
Input: [1,2,3]
Output: [2, 1]
Explanation: 2 has the smallest even value, and 2 has the smallest index.

Example 3:
Input: []
Output: []

Example 4:
Input: [5, 0, 3, 0, 4, 2]
Output: [0, 1]
Explanation: 0 is the smallest value, but there are two zeros,
so we will choose the first zero, which has the smallest index.

Constraints:
* 1 <= nodes.length <= 10000
* 0 <= node.value
*)
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.


(* pluck 函数的程序规约 *)

Require Import Coq.ZArith.ZArith.
From AUXLib Require Import ListLib.

Local Open Scope Z_scope.

Definition list_nonnegative (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0.

Definition output_Z_to_option (l : list Z) : option (nat * nat) :=
  match l with
  | [] => None
  | value :: index :: [] => Some (Z.to_nat value, Z.to_nat index)
  | _ => None
  end.

Definition problem_68_pre (arr : list Z) : Prop :=
  True.

Definition pluck_update (x i : Z) (best : list Z) : list Z :=
  if Z.eqb (Z.rem x 2) 0 then
    match best with
    | [] => [x; i]
    | value :: _ =>
        if Z.ltb x value then [x; i] else best
    end
  else best.

Fixpoint pluck_scan_from (i : Z) (arr best : list Z) : list Z :=
  match arr with
  | [] => best
  | x :: xs => pluck_scan_from (i + 1) xs (pluck_update x i best)
  end.

Definition pluck_prefix_result (arr : list Z) (i : Z) : list Z :=
  pluck_scan_from 0 (sublist 0 i arr) [].

Definition pluck_loop_state (arr : list Z) (i : Z) (output : list Z) : Prop :=
  0 <= i <= Zlength arr /\
  output = pluck_prefix_result arr i.

Definition pluck_best_spec (base : Z) (processed best : list Z) : Prop :=
  match best with
  | [] =>
      forall x, In x processed -> Z.rem x 2 <> 0
  | value :: index :: [] =>
      exists idx : nat,
        index = base + Z.of_nat idx /\
        nth_error processed idx = Some value /\
        Z.rem value 2 = 0 /\
        (forall x, In x processed -> Z.rem x 2 = 0 -> value <= x) /\
        (forall j : nat, (j < idx)%nat -> nth j processed 0 <> value)
  | _ => False
  end.

Definition problem_68_spec (arr output : list Z) : Prop :=
  list_nonnegative arr /\
  pluck_best_spec 0 arr output.


(* Ground-truth proof helpers. *)

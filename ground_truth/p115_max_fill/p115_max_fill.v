(* You are given a rectangular grid of wells. Each row represents a single well,
and each 1 in a row represents a single unit of water.
Each well has a corresponding bucket that can be used to extract water from it,
and all buckets have the same capacity.
Your task is to use the buckets to empty the wells.
Output the number of times you need to lower the buckets.

Example 1:
Input:
grid : [[0,0,1,0], [0,1,0,0], [1,1,1,1]]
bucket_capacity : 1
Output: 6

Example 2:
Input:
grid : [[0,0,1,1], [0,0,0,0], [1,1,1,1], [0,1,1,1]]
bucket_capacity : 2
Output: 5

Example 3:
Input:
grid : [[0,0,0], [0,0,0]]
bucket_capacity : 5
Output: 0

Constraints:
* all wells have the same length
* 1 <= grid.length <= 10^2
* 1 <= grid[:,1].length <= 10^2
* grid[i][j] -> 0 | 1
* 1 <= capacity <= 10
*)

Require Import Coq.Lists.List Coq.Arith.Arith.
Import ListNotations.

Definition count_water (well : list nat) : nat :=
  fold_left Nat.add well 0.

Definition required_trips_impl (grid : list (list nat)) (bucket_capacity : nat) : nat :=
  fold_left
    (fun acc well =>
      let w := count_water well in
      acc + (w + bucket_capacity - 1) / bucket_capacity)
    grid
    0.

(* grid 非空；所有行长度一致且在 [1,100]；元素为 0 或 1；容量在 [1,10] *)
Definition problem_115_pre (grid : list (list nat)) (bucket_capacity : nat) : Prop :=
  grid <> [] /\
  bucket_capacity >= 1 /\ bucket_capacity <= 10 /\
  let len_first := length (hd [] grid) in
  len_first >= 1 /\ len_first <= 100 /\
  Forall (fun row => length row = len_first /\ Forall (fun x => x = 0 \/ x = 1) row) grid /\
  length grid >= 1 /\ length grid <= 100.

Definition problem_115_spec (grid : list (list nat)) (bucket_capacity : nat) (output : nat) : Prop :=
  output = required_trips_impl grid bucket_capacity.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
From AUXLib Require Import ListLib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Fixpoint sum_z (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => x + sum_z xs
  end.

Definition nat_row_of_z (row : list Z) : list nat :=
  map Z.to_nat row.

Definition nat_grid_of_z (rows : list (list Z)) : list (list nat) :=
  map nat_row_of_z rows.

Definition problem_115_pre_z (rows : list (list Z)) (capacity : Z) : Prop :=
  problem_115_pre (nat_grid_of_z rows) (Z.to_nat capacity).

Definition problem_115_spec_z (rows : list (list Z)) (capacity ret : Z) : Prop :=
  problem_115_spec (nat_grid_of_z rows) (Z.to_nat capacity) (Z.to_nat ret).

Definition row_sum_prefix_z (row : list Z) (j : Z) : Z :=
  sum_z (firstn (Z.to_nat j) row).

Definition row_trip_z (row : list Z) (capacity : Z) : Z :=
  let s := sum_z row in
  if s =? 0 then 0 else Z.quot (s - 1) capacity + 1.

Definition trips_prefix_z (rows : list (list Z)) (i capacity : Z) : Z :=
  fold_left Z.add
    (map (fun row => row_trip_z row capacity) (firstn (Z.to_nat i) rows))
    0.

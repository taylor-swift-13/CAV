(*Given a grid with N rows and N columns (N >= 2) and a positive integer k,
each cell of the grid contains a value. Every integer in the range [1, N * N]
inclusive appears exactly once on the cells of the grid.
You have to find the minimum path of length k in the grid. You can start
from any cell, and in each step you can move to any of the neighbor cells,
in other words, you can go to cells which share an edge with you current
cell.
Please note that a path of length k means visiting exactly k cells (not
necessarily distinct).
You CANNOT go off the grid.
A path A (of length k) is considered less than a path B (of length k) if
after making the ordered lists of the values on the cells that A and B go
through (let's call them lst_A and lst_B), lst_A is lexicographically less
than lst_B, in other words, there exist an integer index i (1 <= i <= k)
such that lst_A[i] < lst_B[i] and for any j (1 <= j < i) we have
lst_A[j] = lst_B[j].
It is guaranteed that the answer is unique.
Return an ordered list of the values on the cells that the minimum path go through.

Examples:

Input: grid = [ [1,2,3], [4,5,6], [7,8,9]], k = 3
Output: [1, 2, 1]

Input: grid = [ [5,9,3], [4,1,6], [7,8,2]], k = 1
Output: [1] *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Import ListNotations.

Definition Grid := list (list nat).
Definition Pos := (nat * nat)%type.

Definition grid_cell (grid : Grid) (r c : nat) : nat :=
  nth c (nth r grid []) 0.

Definition cell_value (grid : Grid) (p : Pos) (v : nat) : Prop :=
  grid_cell grid (fst p) (snd p) = v.

Definition neighbor_min_at
    (grid : Grid) (n r c m : nat) : Prop :=
  r < n /\
  c < n /\
  grid_cell grid r c = 1 /\
  ((0 < r /\ m = grid_cell grid (r - 1) c) \/
   (S r < n /\ m = grid_cell grid (S r) c) \/
   (0 < c /\ m = grid_cell grid r (c - 1)) \/
   (S c < n /\ m = grid_cell grid r (S c))) /\
  (0 < r -> m <= grid_cell grid (r - 1) c) /\
  (S r < n -> m <= grid_cell grid (S r) c) /\
  (0 < c -> m <= grid_cell grid r (c - 1)) /\
  (S c < n -> m <= grid_cell grid r (S c)).

Definition is_neighbor_min_of_one (grid : Grid) (m : nat) : Prop :=
  exists n r c,
    length grid = n /\
    Forall (fun row => length row = n) grid /\
    neighbor_min_at grid n r c m.

Definition alternating_min_path_values (k m : nat) (output : list nat) : Prop :=
  length output = k /\
  forall i,
    i < k ->
    nth_error output i =
      Some (if Nat.even i then 1 else m).

Definition square_permutation_grid (grid : Grid) (n : nat) : Prop :=
  2 <= n /\
  length grid = n /\
  Forall (fun row => length row = n) grid /\
  Permutation (concat grid) (seq 1 (n * n)).

Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  1 <= k /\
  exists n, square_permutation_grid grid n.

Definition problem_129_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  exists m,
    is_neighbor_min_of_one grid m /\
    alternating_min_path_values k m output.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Import ListNotations.

Local Open Scope Z_scope.

Definition nat_row_of_z_129 (row : list Z) : list nat :=
  map Z.to_nat row.

Definition nat_grid_of_z_129 (rows : list (list Z)) : list (list nat) :=
  map nat_row_of_z_129 rows.

Definition nat_list_of_z_129 (xs : list Z) : list nat :=
  map Z.to_nat xs.

Definition problem_129_pre_z (rows : list (list Z)) (k : Z) : Prop :=
  0 <= k /\ problem_129_pre (nat_grid_of_z_129 rows) (Z.to_nat k).

Definition problem_129_spec_z (rows : list (list Z)) (k : Z) (output : list Z) : Prop :=
  0 <= k /\ problem_129_spec (nat_grid_of_z_129 rows) (Z.to_nat k) (nat_list_of_z_129 output).

Definition cell_value_z_129 (rows : list (list Z)) (x y v : Z) : Prop :=
  0 <= x /\ 0 <= y /\
  cell_value (nat_grid_of_z_129 rows) (Z.to_nat x, Z.to_nat y) (Z.to_nat v).

Definition one_pos_z_129 (rows : list (list Z)) (x y : Z) : Prop :=
  0 <= x /\ 0 <= y /\ Znth y (Znth x rows nil) 0 = 1.

Definition scanned_before_129 (n i j r c : Z) : Prop :=
  0 <= r < n /\
  0 <= c < n /\
  (r < i \/ (r = i /\ c < j)).

Definition no_one_before_129 (rows : list (list Z)) (n i j : Z) : Prop :=
  forall r c,
    scanned_before_129 n i j r c ->
    Znth c (Znth r rows nil) 0 <> 1.

Definition find_one_scan_state_129
    (rows : list (list Z)) (n i j x y : Z) : Prop :=
  0 <= i <= n /\
  0 <= j <= n /\
  0 <= x < n /\
  0 <= y < n /\
  (one_pos_z_129 rows x y \/ no_one_before_129 rows n i j).

Definition neighbor_min_z_129 (rows : list (list Z)) (x y minv : Z) : Prop :=
  0 <= x /\ 0 <= y /\ 0 <= minv /\
  cell_value (nat_grid_of_z_129 rows) (Z.to_nat x, Z.to_nat y) 1 /\
  is_neighbor_min_of_one (nat_grid_of_z_129 rows) (Z.to_nat minv).

Definition output_value_129 (i minv : Z) : Z :=
  if Z.even i then 1 else minv.

Definition output_prefix_129 (k minv i : Z) (output : list Z) : Prop :=
  0 <= i <= k /\
  Zlength output = i /\
  forall t, 0 <= t < i -> Znth t output 0 = output_value_129 t minv.

Definition dir_neighbor_value_129
    (rows : list (list Z)) (n x y d v : Z) : Prop :=
  (d = 0 /\ 0 < x /\ x < n /\ 0 <= y < n /\
     v = Znth y (Znth (x - 1) rows nil) 0) \/
  (d = 1 /\ 0 <= x /\ x + 1 < n /\ 0 <= y < n /\
     v = Znth y (Znth (x + 1) rows nil) 0) \/
  (d = 2 /\ 0 <= x < n /\ 0 < y /\ y < n /\
     v = Znth (y - 1) (Znth x rows nil) 0) \/
  (d = 3 /\ 0 <= x < n /\ 0 <= y /\ y + 1 < n /\
     v = Znth (y + 1) (Znth x rows nil) 0).

Definition checked_neighbor_min_129
    (rows : list (list Z)) (n x y stage minv : Z) : Prop :=
  0 <= stage <= 4 /\
  0 <= x < n /\
  0 <= y < n /\
  1 <= minv <= n * n /\
  (forall d v,
      0 <= d < stage ->
      dir_neighbor_value_129 rows n x y d v ->
      minv <= v) /\
  (minv = n * n \/
   exists d v,
     0 <= d < stage /\
     dir_neighbor_value_129 rows n x y d v /\
     minv = v).

Definition find_one_state_129 (rows : list (list Z)) (n i j x y : Z) : Prop :=
  0 <= i <= n /\
  0 <= j <= n /\
  0 <= x < n /\
  0 <= y < n /\
  one_pos_z_129 rows x y.

Definition min_neighbor_state_129 (rows : list (list Z)) (n x y minv : Z) : Prop :=
  checked_neighbor_min_129 rows n x y 4 minv /\
  is_neighbor_min_of_one (nat_grid_of_z_129 rows) (Z.to_nat minv).

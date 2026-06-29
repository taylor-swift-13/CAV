(* def get_row(lst, x):
"""
You are given a 2 dimensional data, as a nested lists,
which is similar to matrix, however, unlike matrices,
each row may contain a different number of columns.
Given lst, and integer x, find integers x in the list,
and return list of tuples, [(x1, y1), (x2, y2) ...] such that
each tuple is a coordinate - (row, columns), starting with 0.
Sort coordinates initially by rows in ascending order.
Also, sort coordinates of the row by columns in descending order.

Examples:
get_row([
[1,2,3,4,5,6],
[1,2,3,4,1,6],
[1,2,3,4,5,1]
], 1) == [(0, 0), (1, 4), (1, 0), (2, 5), (2, 0)]
get_row([], 1) == []
get_row([[], [1], [1, 2, 3]], 3) == [(2, 2)]
""" *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

(*
 * 排序关系定义：
 * - 首先按行号 (r) 升序。
 * - 如果行号相同，则按列号 (c) 降序。
 *)
Inductive coord_order (c1 c2 : Z * Z) : Prop :=
  | row_lt : fst c1 < fst c2 -> coord_order c1 c2
  | col_gt : fst c1 = fst c2 -> snd c1 > snd c2 -> coord_order c1 c2.

(*
 * 检查一个坐标列表是否根据 coord_order 关系进行了排序。
 * 这个版本可以通过 Coq 的终止性检查。
 *)
Fixpoint is_sorted (l : list (Z * Z)) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | c1 :: (c2 :: _ as tail) => coord_order c1 c2 /\ is_sorted tail
  end.

Fixpoint collect_coords_row (row : list Z) (r c : Z) (x : Z) : list (Z * Z) :=
  match row with
  | [] => []
  | h :: t =>
      if Z.eqb h x then
        (r, c) :: collect_coords_row t r (Z.succ c) x
      else
        collect_coords_row t r (Z.succ c) x
  end.

Fixpoint collect_all_coords (lst : list (list Z)) (r : Z) (x : Z) : list (Z * Z) :=
  match lst with
  | [] => []
  | row :: rest =>
      collect_coords_row row r 0 x ++ collect_all_coords rest (Z.succ r) x
  end.

Fixpoint insert_coord (coord : Z * Z) (coords : list (Z * Z)) : list (Z * Z) :=
  match coords with
  | [] => [coord]
  | h :: t =>
      if Z.ltb (fst coord) (fst h) then
        coord :: coords
      else if Z.eqb (fst coord) (fst h) then
        if Z.ltb (snd h) (snd coord) then
          coord :: coords
        else
          h :: insert_coord coord t
      else
        h :: insert_coord coord t
  end.

Fixpoint sort_coords (coords : list (Z * Z)) : list (Z * Z) :=
  match coords with
  | [] => []
  | h :: t => insert_coord h (sort_coords t)
  end.

Definition get_row_impl (lst : list (list Z)) (x : Z) : list (Z * Z) :=
  sort_coords (collect_all_coords lst 0 x).

Definition problem_87_pre (lst : list (list Z)) (x : Z) : Prop := True.

Definition problem_87_spec (lst : list (list Z)) (x : Z) (res : list (Z * Z)) : Prop :=
  res = get_row_impl lst x.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
From AUXLib Require Import ListLib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Fixpoint flatten_coords_87 (coords : list (Z * Z)) : list Z :=
  match coords with
  | [] => []
  | (r, c) :: rest => r :: c :: flatten_coords_87 rest
  end.

Definition problem_87_pre_z (rows : list (list Z)) (x : Z) : Prop :=
  problem_87_pre rows x.

Definition problem_87_spec_z
    (rows : list (list Z)) (x : Z) (output : list Z) : Prop :=
  exists coords,
    problem_87_spec rows x coords /\
    output = flatten_coords_87 coords.

Definition row_sizes_match_87
    (rows : list (list Z)) (sizes : list Z) : Prop :=
  Zlength sizes = Zlength rows /\
  forall i,
    0 <= i < Zlength rows ->
    Znth i sizes 0 = Zlength (Znth i rows nil).

Definition total_cells_prefix_87 (rows : list (list Z)) (i : Z) : Z :=
  fold_left Z.add
    (map (fun row => Zlength row) (firstn (Z.to_nat i) rows)) 0.

Definition coord_if_87 (row : list Z) (r x c : Z) : list (Z * Z) :=
  if Znth c row 0 =? x then [(r, c)] else [].

Definition desc_cols_after_87 (row : list Z) (j : Z) : list Z :=
  rev (map Z.of_nat
         (seq (Z.to_nat (j + 1))
              (Z.to_nat (Zlength row - (j + 1))))).

Fixpoint collect_coords_row_desc_87
    (row : list Z) (r c x : Z) : list (Z * Z) :=
  match row with
  | [] => []
  | h :: t =>
      collect_coords_row_desc_87 t r (Z.succ c) x ++
      if h =? x then [(r, c)] else []
  end.

Definition row_desc_after_87 (row : list Z) (r j x : Z) : list (Z * Z) :=
  collect_coords_row_desc_87 (skipn (Z.to_nat (j + 1)) row) r (j + 1) x.

Definition scan_coords_87
    (rows : list (list Z)) (x i j : Z) : list (Z * Z) :=
  sort_coords (collect_all_coords (firstn (Z.to_nat i) rows) 0 x) ++
  row_desc_after_87 (Znth i rows nil) i j x.

Definition scan_state_87
    (rows : list (list Z)) (x i j : Z) (output : list Z) : Prop :=
  if i <? Zlength rows then
    output = flatten_coords_87 (scan_coords_87 rows x i j)
  else
    output = flatten_coords_87 (get_row_impl rows x).

Definition prefix_state_87
    (rows : list (list Z)) (x i : Z) (output : list Z) : Prop :=
  output =
    flatten_coords_87
      (sort_coords (collect_all_coords (firstn (Z.to_nat i) rows) 0 x)).

Fixpoint collect_all_coords_desc_87
    (rows : list (list Z)) (r x : Z) : list (Z * Z) :=
  match rows with
  | [] => []
  | row :: rest =>
      collect_coords_row_desc_87 row r 0 x ++
      collect_all_coords_desc_87 rest (Z.succ r) x
  end.

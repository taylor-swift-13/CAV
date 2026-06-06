(* spec/58 *)
(* def common(l1: list, l2: list):
"""Return sorted unique common elements for two lists.
>>> common([1, 4, 3, 34, 653, 2, 5], [5, 7, 1, 5, 9, 653, 121])
[1, 5, 653]
>>> common([5, 3, 2, 8], [3, 2])
[2, 3]

""" *)
Require Import Coq.ZArith.ZArith. (* 导入整数库，提供 Z 类型和 Z.le *)
Require Import Coq.Lists.List.      (* 导入列表库 *)
Require Import Sorting.Sorted.
Import ListNotations.

(*
 *
 * 描述了输入列表 l1, l2 与输出列表 l_out 之间的关系。
 *)
(* Pre: no special constraints for `common` *)


Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import ListLib.

Local Open Scope Z_scope.

Definition problem_58_pre (l1 l2 : list Z) : Prop :=
  True.

Definition problem_58_spec (l1 l2 output : list Z) : Prop :=
  (((* 条件1: 公共性与完备性 *)
    (* output 中的任意整数 x，当且仅当 x 同时在 l1 和 l2 中。*)
    (forall x: Z, In x output <-> (In x l1 /\ In x l2)) /\
  
    (* 条件2: 有序性 *)
    (* output 是根据整数的小于等于关系 (Z.le) 排序的。 *)
    Sorted Z.le output /\
  
    (* 条件3: 唯一性 *)
    (* output 中没有重复元素。 *)
    NoDup output)%nat).

Definition list_contains (x : Z) (l : list Z) : Prop :=
  In x l.

Definition list_not_contains (x : Z) (l : list Z) : Prop :=
  ~ In x l.

Fixpoint common_values_aux (seen rest l2 : list Z) : list Z :=
  match rest with
  | [] => seen
  | x :: xs =>
      if in_dec Z.eq_dec x seen then
        common_values_aux seen xs l2
      else if in_dec Z.eq_dec x l2 then
        common_values_aux (seen ++ [x]) xs l2
      else
        common_values_aux seen xs l2
  end.

Definition common_values (l1 l2 : list Z) : list Z :=
  common_values_aux [] l1 l2.

Definition common_first_loop
  (l1 l2 : list Z) (i : Z) (output : list Z) : Prop :=
  0 <= i <= Zlength l1 /\
  output = common_values (sublist 0 i l1) l2.

Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
  if Z.eqb ascending 0 then True else Sorted Z.le l.

(* spec/34 *)
(* Return sorted unique elements in a list
>>> unique([5, 3, 5, 2, 3, 3, 9, 0, 123])
[0, 2, 3, 5, 9, 123] *)

(* Spec(input : list int, output : list int) :=
	IsSorted(output) /\
	IsUnique(output) /\
	∀i ∈ output <-> i ∈ input
	 *)

Require Import Coq.Lists.List.      (* 提供列表基本定义，如 In, NoDup *)
Require Import Coq.ZArith.ZArith.    (* 提供整数类型 Z 及其操作 *)
Require Import Coq.Sorting.Sorted.    (* 提供 Sorted 的定义 *)
Import ListNotations.

(* Pre: no additional constraints for `unique` by default *)

(*
  规约 Spec(input, output) 定义了 "output 是 input 的排序后去重版本"
*)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import ListLib.

Local Open Scope Z_scope.

Definition problem_34_pre (input : list Z) : Prop :=
  True.

Definition problem_34_spec (input output : list Z) : Prop :=
  ((* 1. 输出列表是根据小于等于 (Z.le) 关系排序的 *)
    Sorted Z.le output /\

    (* 2. 输出列表中的元素是唯一的 *)
    NoDup output /\

    (* 3. 输入和输出列表包含相同的元素集合。
       这通过双向蕴含来保证：
       - 输入中的任何元素都必须出现在输出中。
       - 输出中的任何元素都必须来源于输入。
    *)
    (forall z, In z input <-> In z output)).

Definition list_contains (x : Z) (l : list Z) : Prop :=
  In x l.

Definition list_not_contains (x : Z) (l : list Z) : Prop :=
  ~ In x l.

Fixpoint seen_values_aux (seen rest : list Z) : list Z :=
  match rest with
  | [] => seen
  | x :: xs =>
      if in_dec Z.eq_dec x seen
      then seen_values_aux seen xs
      else seen_values_aux (seen ++ [x]) xs
  end.

Definition seen_values (l : list Z) : list Z :=
  seen_values_aux [] l.

Definition unique_first_loop (input : list Z) (i : Z) (output : list Z) : Prop :=
  0 <= i <= Zlength input /\
  output = seen_values (sublist 0 i input).

Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
  if Z.eqb ascending 0 then True else Sorted Z.le l.

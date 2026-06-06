(* spec/120 *)
(*Given an array arr of integers and a positive integer k, return a sorted list
of length k with the maximum k numbers in arr.

Example 1:

Input: arr = [-3, -4, 5], k = 3
Output: [-4, -3, 5]

Example 2:

Input: arr = [4, -4, 4], k = 2
Output: [4, 4]

Example 3:

Input: arr = [-3, 2, 1, 2, -1, -2, 1], k = 1
Output: [2]

Note:
1. The length of the array will be in the range of [1, 1000].
2. The elements in the array will be in the range of [-1000, 1000].
3. 0 <= k <= len(arr) *)

(* 引入所需的Coq库 *)
Require Import Coq.Lists.List.      (* List基本操作 *)
Require Import Coq.ZArith.ZArith.    (* 整数Z *)
Require Import Coq.Sorting.Permutation. (* Permutation定义 *)
Require Import Coq.Sorting.Sorted.      (* Sorted定义 *)
Import ListNotations.
(* 打开整数和列表的作用域以便使用相关操作符 *)
Open Scope Z_scope.
Open Scope list_scope.

(* 约束：1 <= length arr <= 1000；元素绝对值 <= 1000；0 <= k <= length arr *)

(*
 * @brief 程序规约：top_k_spec
 * @param arr 输入的整数列表
 * @param k   需要选出的最大元素数量
 * @param res 输出的结果列表
 *
 * 这个规约断言 res 是 arr 中 k 个最大元素的有序列表。
 *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.

Definition problem_120_pre (arr : list Z) (k : Z) : Prop :=
  1 <= Zlength arr <= 1000 /\
  Forall (fun z => -1000 <= z <= 1000) arr /\
  0 <= k <= Zlength arr.

Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
  if Z.eqb ascending 0 then True else Sorted Z.le l.

Definition copy_prefix (input : list Z) (i : Z) : list Z :=
  sublist 0 i input.

Definition maximum_output_prefix (sorted_l : list Z) (size k i : Z) : list Z :=
  sublist (size - k) (size - k + i) sorted_l.

Definition problem_120_spec (input : list Z) (k : Z) (output : list Z) : Prop :=
  ((* 1. 输出列表的长度必须为 k *)
    Zlength output = k /\
  
    (* 2. 输出列表必须是升序排列的 *)
    Sorted Z.le output /\
  
    (* 3. 存在一个 "剩余" 列表 rest_of_arr，它包含 input 中所有未被选入 output 的元素 *)
    (exists rest_of_arr,
      (* 3a. output 和 rest_of_arr 的组合是原始列表 input 的一个排列组合。
             这确保了 output 中的所有元素都来自 input，且元素的数量/重复次数正确。 *)
      Permutation (output ++ rest_of_arr) input /\
  
      (* 3b. output 中的任何元素都必须大于或等于 rest_of_arr 中的任何元素。
             这确保了 output 包含的是 k 个最大的数。 *)
      (forall x y, In x output -> In y rest_of_arr -> y <= x))).

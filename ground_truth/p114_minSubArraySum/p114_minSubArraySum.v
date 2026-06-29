(* spec/114 *)
(* Given an array of integers nums, find the minimum sum of any non-empty sub-array
of nums.
Example
minSubArraySum([2, 3, 4, 1, 2, 4]) == 1
minSubArraySum([-1, -2, -3]) == -6 *)

(* 引入所需的库 *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.
(* 定义一个函数来计算整数列表的和 *)
Definition list_sum (l : list Z) : Z :=
  fold_left Z.add l 0.

(* nums 非空 *)

(* 定义一个规约来描述最小子数组和的属性 *)

Definition list_sum_Z_114 := list_sum.

Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition LLONG_MIN : Z := -9223372036854775808.
Definition LLONG_MAX : Z := 9223372036854775807.

Definition problem_114_pre (nums : list Z) : Prop :=
  (nums) <> [].

Fixpoint min_suffix_prefix_nat (n : nat) (nums : list Z) : Z :=
  match n with
  | O => 0
  | S O => Znth 0 nums 0
  | S n' =>
      let prev := min_suffix_prefix_nat n' nums in
      let x := Znth (Z.of_nat n') nums 0 in
      if Z.ltb prev 0 then prev + x else x
  end.

Definition min_suffix_prefix (i : Z) (nums : list Z) : Z :=
  min_suffix_prefix_nat (Z.to_nat i) nums.

Fixpoint min_subarray_prefix_nat (n : nat) (nums : list Z) : Z :=
  match n with
  | O => 0
  | S O => Znth 0 nums 0
  | S n' =>
      let prev_min := min_subarray_prefix_nat n' nums in
      let cur := min_suffix_prefix_nat (S n') nums in
      if Z.ltb cur prev_min then cur else prev_min
  end.

Definition min_subarray_prefix (i : Z) (nums : list Z) : Z :=
  min_subarray_prefix_nat (Z.to_nat i) nums.

Definition problem_114_spec (nums : list Z) (result : Z) : Prop :=
  ((* 1. 存在性 (Existence): 必须存在一个非空子数组，其和等于 result *)
    (exists sub_array,
      sub_array <> [] /\
      (exists prefix suffix, nums = prefix ++ sub_array ++ suffix) /\
      list_sum sub_array = result)
    /\
    (* 2. 最小性 (Minimality): 对于所有非空的子数组，它们的和都必须大于或等于 result *)
    (forall sub_array,
      sub_array <> [] ->
      (exists prefix suffix, nums = prefix ++ sub_array ++ suffix) ->
      result <= list_sum sub_array)).

Definition zsum_114 (l : list Z) : Z :=
  fold_left Z.add l 0.

Definition suffix_min_spec (nums : list Z) (result : Z) : Prop :=
  (exists suffix prefix,
      suffix <> [] /\
      nums = prefix ++ suffix /\
      zsum_114 suffix = result) /\
  (forall suffix prefix,
      suffix <> [] ->
      nums = prefix ++ suffix ->
      result <= zsum_114 suffix).

Definition subarray_min_spec_114 (nums : list Z) (result : Z) : Prop :=
  (exists sub_array,
    sub_array <> [] /\
    (exists prefix suffix, nums = prefix ++ sub_array ++ suffix) /\
    zsum_114 sub_array = result) /\
  (forall sub_array,
    sub_array <> [] ->
    (exists prefix suffix, nums = prefix ++ sub_array ++ suffix) ->
    result <= zsum_114 sub_array).

Definition list_int64_range (nums : list Z) : Prop :=
  forall i, 0 <= i < Zlength nums -> LLONG_MIN <= Znth i nums 0 <= LLONG_MAX.

Definition kadane_int64_range (nums : list Z) : Prop :=
  list_int64_range nums /\
  (forall i,
      1 <= i < Zlength nums ->
      LLONG_MIN <= min_suffix_prefix i nums + Znth i nums 0 <= LLONG_MAX) /\
  (forall i,
      1 <= i <= Zlength nums ->
      LLONG_MIN <= min_suffix_prefix i nums <= LLONG_MAX /\
      LLONG_MIN <= min_subarray_prefix i nums <= LLONG_MAX).

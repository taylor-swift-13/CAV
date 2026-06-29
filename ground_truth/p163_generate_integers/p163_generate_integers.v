(* spec/163 *)
(* def generate_integers(a, b):
"""
Given two positive integers a and b, return the even digits between a
and b, in ascending order.

For example:
generate_integers(2, 8) => [2, 4, 6, 8]
generate_integers(8, 2) => [2, 4, 6, 8]
generate_integers(10, 14) => []
""" *)
(* 引入所需的基础库 *)
Require Import Coq.Lists.List.      (* List 定义与操作 *)
Require Import Coq.Arith.Arith.      (* 算术相关，包含 min, max, le, lt 等 *)
Require Import Coq.Sorting.Sorted.  (* Sorted 定义 *)
Require Import Coq.Lists.SetoidList.  (* NoDup 定义 *)
Import ListNotations.

(*
  generate_integers_spec 是函数 generate_integers 的程序规约。

  - a, b: 输入的两个自然数。
  - l: 输出的结果列表。

  该规约使用一阶逻辑精确地描述了输入 a, b 与输出列表 l 之间应满足的关系。
*)
(* 输入为正整数 *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition digit_candidates : list Z := [2; 4; 6; 8].

Definition generate_prefix_list (lo i : Z) : list Z :=
  filter (fun d => andb (lo <=? d) (d <? i)) digit_candidates.

Definition generate_list (lo hi : Z) : list Z :=
  generate_prefix_list lo (hi + 1).

Definition generate_bounds (a0 b0 a b : Z) : Prop :=
  a = Z.min a0 b0 /\ b = Z.max a0 b0.

Definition z_min (a b : Z) : Z := Z.min a b.

Definition z_max (a b : Z) : Z := Z.max a b.

Definition generate_prefix (lo i hi : Z) (output : list Z) : Prop :=
  lo <= i <= hi + 1 /\
  output = generate_prefix_list lo i.

Definition problem_163_pre (a b : Z) : Prop :=
  a > 0 /\ b > 0.

Definition problem_163_spec (a b : Z) (output : list Z) : Prop :=
  (forall d : Z,
    In d output <->
      Z.min a b <= d <= Z.max a b /\ d < 10 /\ d mod 2 = 0) /\
  Sorted Z.le output /\
  NoDup output.

(* Helper lemmas migrated from the old proof, with names aligned to the input spec. *)

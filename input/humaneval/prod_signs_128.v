(* spec/128 *)
(*You are given an array arr of integers and you need to return
sum of magnitudes of integers multiplied by product of all signs
of each number in the array, represented by 1, -1 or 0.
Note: return None for empty arr.

Example:
>>> prod_signs([1, 2, 2, -4]) == -9
>>> prod_signs([0, 1]) == 0
>>> prod_signs([]) == None *)

(* 引入所需的库 *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

(* 输入可为空或任意整数列表 *)
(*
  程序规约 (Specification) 定义了输入 `arr` (一个整数列表)
  与输出 `output` (一个可选的整数) 之间的关系。
*)

Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import naive_C_Rules.
Local Open Scope Z_scope.

Definition sum_abs_prefix (i : Z) (l : list Z) : Z :=
  fold_right Z.add 0 (map Z.abs (sublist 0 i l)).

Definition prod_sgn_prefix (i : Z) (l : list Z) : Z :=
  fold_right Z.mul 1 (map Z.sgn (sublist 0 i l)).

Definition prod_signs_prefix (i : Z) (l : list Z) (sum prods : Z) : Prop :=
  0 <= i <= Zlength l /\
  sum = sum_abs_prefix i l /\
  prods = prod_sgn_prefix i l.

Definition prod_signs_int_range (l : list Z) : Prop :=
  (forall i,
      0 <= i < Zlength l ->
      INT_MIN < Znth i l 0 <= INT_MAX) /\
  (forall i,
      0 <= i <= Zlength l ->
      0 <= sum_abs_prefix i l <= INT_MAX).

Definition problem_128_pre (l : list Z) : Prop :=
  True.

Definition problem_128_spec (l : list Z) (out : Z) : Prop :=
  match l with
      | nil => out = -32768
      | _ :: _ => (let arr := l in let output := (Some out) in (* 对输入列表进行模式匹配 *)
    match arr with
    (* 情况1: 如果列表为空 *)
    | [] =>
      (* 规约要求输出必须是 None *)
      output = None
  
    (* 情况2: 如果列表非空 *)
    | _ :: _ =>
      (* 使用 let ... in ... 结构来定义中间计算 *)
      (* 计算列表中所有元素绝对值的和 *)
      let sum_mags := fold_right Z.add 0 (map Z.abs arr) in
      (* 计算列表中所有元素符号的乘积 *)
      let prod_sgs := fold_right Z.mul 1 (map Z.sgn arr) in
      (* 规约要求输出必须是 Some (和 * 积) *)
      output = Some (sum_mags * prod_sgs)
    end)
      end. 

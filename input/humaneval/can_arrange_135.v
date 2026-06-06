(* spec/135 *)
(* def can_arrange(arr):
Create a function which returns the largest index of an element which
is not greater than or equal to the element immediately preceding it. If
no such element exists then return -1. The given array will not contain
duplicate values.

Examples:
can_arrange([1,2,4,3,5]) = 3
can_arrange([1,2,3]) = -1 *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

(* 辅助：在位置 k (nat) 满足 C 程序中的条件 arr[k] <= k。 *)
Definition can_arrange_at (lst : list Z) (k : nat) : Prop :=
  (k < length lst)%nat /\
  match nth_error lst k with
  | Some x => (x <= Z.of_nat k)%Z
  | None => False
  end.

(* 输入数组不包含重复元素 *)

(* 最终 Spec：
   - 若 r = -1，则不存在任何 k 使得 can_arrange_at lst k 成立；
   - 否则存在一个自然数 k，使 r = Z.of_nat k 且 can_arrange_at lst k，
     并且 k 是满足 can_arrange_at 的最大索引。 *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition can_arrange_hit (l : list Z) (i : Z) : Prop :=
  0 <= i < Zlength l /\ Znth i l 0 <= i.

Definition can_arrange_prefix (i : Z) (l : list Z) (max : Z) : Prop :=
  0 <= i <= Zlength l /\
  -1 <= max < i /\
  (max = -1 \/ can_arrange_hit l max) /\
  (forall j, 0 <= j < i -> can_arrange_hit l j -> j <= max).

Definition problem_135_pre (l : list Z) : Prop :=
  NoDup (l).

Definition problem_135_spec (l : list Z) (r : Z) : Prop :=
  ((r = -1 /\ (forall k, ~ can_arrange_at l k))
    \/
    (exists k : nat,
        r = Z.of_nat k /\
        can_arrange_at l k /\
        (forall j : nat, can_arrange_at l j -> (j <= k)%nat))).
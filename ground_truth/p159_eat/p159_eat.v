(* spec/159 *)
(* def eat(number, need, remaining):
"""
You're a hungry rabbit. Return [total eaten after meals, remaining after meals].
If not enough remaining, eat all remaining (still hungry).
Example: eat(5,6,10)->[11,4]  eat(2,11,5)->[7,0]
Constrain: 0 <= number,need,remaining <= 1000
""" *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Import ListNotations.
Local Open Scope Z_scope.

(* 扁平前条件:界直接可见,证 safety 不必多层 unfold *)
Definition problem_159_pre (number need remaining : Z) : Prop :=
  0 <= number <= 1000 /\ 0 <= need <= 1000 /\ 0 <= remaining <= 1000.

(* 结果 = [最终吃掉总数, 最终剩余];够吃则吃 need,不够则吃光 remaining *)
Definition problem_159_spec (number need remaining : Z) (result : list Z) : Prop :=
  (remaining >= need /\ result = (number + need) :: (remaining - need) :: nil) \/
  (remaining < need /\ result = (number + remaining) :: 0 :: nil).

Lemma problem_159_spec_need_gt_remaining : forall number need remaining,
  problem_159_pre number need remaining ->
  need > remaining ->
  problem_159_spec number need remaining [number + remaining; 0].
Proof.
  intros.
  unfold problem_159_spec.
  right.
  split; [lia | reflexivity].
Qed.

Lemma problem_159_spec_need_le_remaining : forall number need remaining,
  problem_159_pre number need remaining ->
  need <= remaining ->
  problem_159_spec number need remaining [number + need; remaining - need].
Proof.
  intros.
  unfold problem_159_spec.
  left.
  split; [lia | reflexivity].
Qed.

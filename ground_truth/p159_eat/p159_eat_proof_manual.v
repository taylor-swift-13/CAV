Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p159_eat Require Import p159_eat_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Lia.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p159_eat.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p159_eat.v so public contract files expose definitions only. *)

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


Lemma proof_of_p159_eat_safety_wit_6 : p159_eat_safety_wit_6.
Proof.
  pre_process.
  unfold problem_159_pre, problem_159_pre in *.
  entailer!.
Qed.

Lemma proof_of_p159_eat_safety_wit_10 : p159_eat_safety_wit_10.
Proof.
  pre_process.
  unfold problem_159_pre, problem_159_pre in *.
  entailer!.
Qed.

Lemma proof_of_p159_eat_safety_wit_12 : p159_eat_safety_wit_12.
Proof.
  pre_process.
  unfold problem_159_pre, problem_159_pre in *.
  entailer!.
Qed.

Lemma proof_of_p159_eat_return_wit_1 : p159_eat_return_wit_1.
Proof.
  pre_process.
  Exists (number_pre + need_pre :: remaining_pre - need_pre :: nil) 2 retval_2.
  sep_apply (IntArray.seg_single retval_2 1 (remaining_pre - need_pre)).
  sep_apply (IntArray.seg_single retval_2 0 (number_pre + need_pre)).
  sep_apply (IntArray.seg_merge_to_full retval_2 0 1 2
               (number_pre + need_pre :: nil)
               (remaining_pre - need_pre :: nil)); [ | lia ].
  entailer!.
  - replace (retval_2 + 0 * sizeof (INT)) with retval_2 by lia.
    replace (2 - 0) with 2 by lia.
    simpl.
    entailer!.
  - apply problem_159_spec_need_le_remaining; auto.
Qed.

Lemma proof_of_p159_eat_return_wit_2 : p159_eat_return_wit_2.
Proof.
  pre_process.
  Exists (number_pre + remaining_pre :: 0 :: nil) 2 retval_2.
  sep_apply (IntArray.seg_single retval_2 1 0).
  sep_apply (IntArray.seg_single retval_2 0 (number_pre + remaining_pre)).
  sep_apply (IntArray.seg_merge_to_full retval_2 0 1 2
               (number_pre + remaining_pre :: nil)
               (0 :: nil)); [ | lia ].
  entailer!.
  - replace (retval_2 + 0 * sizeof (INT)) with retval_2 by lia.
    replace (2 - 0) with 2 by lia.
    simpl.
    entailer!.
  - apply problem_159_spec_need_gt_remaining; auto.
Qed.

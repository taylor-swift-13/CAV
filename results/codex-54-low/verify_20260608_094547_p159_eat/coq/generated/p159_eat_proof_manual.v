Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260608_094547_p159_eat Require Import p159_eat_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p159_eat.
Local Open Scope sac.

Lemma proof_of_p159_eat_safety_wit_6 : p159_eat_safety_wit_6.
Proof.
  pre_process_default.
  entailer!.
  all: unfold problem_159_pre in H3; lia.
Qed.

Lemma proof_of_p159_eat_safety_wit_10 : p159_eat_safety_wit_10.
Proof.
  pre_process_default.
  entailer!.
  all: unfold problem_159_pre in H3; lia.
Qed.

Lemma proof_of_p159_eat_safety_wit_12 : p159_eat_safety_wit_12.
Proof.
  pre_process_default.
  entailer!.
  all: unfold problem_159_pre in H3; lia.
Qed.

Lemma proof_of_p159_eat_return_wit_1 : p159_eat_return_wit_1.
Proof.
  pre_process_default.
  Exists ((number_pre + need_pre) :: (remaining_pre - need_pre) :: nil).
  Exists 2.
  Exists retval_2.
  entailer!.
  - sep_apply_l_atomic (IntArray.seg_single retval_2 1 (remaining_pre - need_pre)).
    sep_apply_l_atomic (IntArray.seg_single retval_2 0 (number_pre + need_pre)).
    sep_apply_l_atomic (IntArray.seg_merge_to_seg retval_2 0 1 2 ((number_pre + need_pre) :: nil) ((remaining_pre - need_pre) :: nil)).
    1: (dump_pre_spatial; lia).
    replace (((number_pre + need_pre) :: nil) ++ ((remaining_pre - need_pre) :: nil))
      with ((number_pre + need_pre) :: (remaining_pre - need_pre) :: nil) by reflexivity.
    sep_apply_l_atomic (IntArray.seg_to_full retval_2 0 2 ((number_pre + need_pre) :: (remaining_pre - need_pre) :: nil)).
    replace (retval_2 + 0 * sizeof (INT)) with retval_2 by lia.
    replace (2 - 0) with 2 by lia.
    cancel.
  - unfold problem_159_spec.
    left.
    split.
    + lia.
    + reflexivity.
Qed.

Lemma proof_of_p159_eat_return_wit_2 : p159_eat_return_wit_2.
Proof.
  pre_process_default.
  Exists ((number_pre + remaining_pre) :: 0 :: nil).
  Exists 2.
  Exists retval_2.
  entailer!.
  - sep_apply_l_atomic (IntArray.seg_single retval_2 1 0).
    sep_apply_l_atomic (IntArray.seg_single retval_2 0 (number_pre + remaining_pre)).
    sep_apply_l_atomic (IntArray.seg_merge_to_seg retval_2 0 1 2 ((number_pre + remaining_pre) :: nil) (0 :: nil)).
    1: (dump_pre_spatial; lia).
    replace (((number_pre + remaining_pre) :: nil) ++ (0 :: nil))
      with ((number_pre + remaining_pre) :: 0 :: nil) by reflexivity.
    sep_apply_l_atomic (IntArray.seg_to_full retval_2 0 2 ((number_pre + remaining_pre) :: 0 :: nil)).
    replace (retval_2 + 0 * sizeof (INT)) with retval_2 by lia.
    replace (2 - 0) with 2 by lia.
    cancel.
  - unfold problem_159_spec.
    right.
    split.
    + lia.
    + reflexivity.
Qed.

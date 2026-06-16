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
From SimpleC.EE.CAV.verify_20260606_203745_p005_intersperse Require Import p005_intersperse_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_p005_intersperse_entail_wit_1 : p005_intersperse_entail_wit_1.
Proof.
  pre_process.
  Exists (Znth 0 l 0 :: nil).
  sep_apply (IntArray.seg_single out_pre 0 (Znth 0 l 0)).
  replace (0 + 1) with 1 by lia.
  replace (2 * 1 - 1) with 1 by lia.
  split_pure_spatial.
  - cancel (IntArray.seg out_pre 0 1 (Znth 0 l 0 :: nil)).
    cancel (IntArray.undef_seg out_pre 1 (2 * numbers_size_pre - 1)).
    cancel (IntArray.full numbers_pre numbers_size_pre l).
  - split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_p005_intersperse_entail_wit_2 : p005_intersperse_entail_wit_2.
Proof.
  pre_process.
  assert (Hk : k = 2 * i - 1) by lia.
  subst k.
  sep_apply_l_atomic (IntArray.undef_missing_i_to_undef_seg_head out_pre (2 * i - 1) (2 * numbers_size_pre - 1)).
  + dump_pre_spatial.
    lia.
  + replace (2 * i - 1 + 1) with (2 * i) in * by lia.
    Exists (app outl (cons delimeter_pre nil)).
    split_pure_spatial.
    - cancel (IntArray.full numbers_pre numbers_size_pre l).
      cancel (IntArray.seg out_pre 0 (2 * i) (app outl (cons delimeter_pre nil))).
      cancel (IntArray.undef_seg out_pre (2 * i) (2 * numbers_size_pre - 1)).
    - split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_p005_intersperse_entail_wit_3 : p005_intersperse_entail_wit_3.
Proof.
  pre_process.
  assert (Hk : k = 2 * i) by lia.
  subst k.
  sep_apply_l_atomic (IntArray.undef_missing_i_to_undef_seg_head out_pre (2 * i) (2 * numbers_size_pre - 1)).
  + dump_pre_spatial.
    lia.
  + replace (2 * i + 1) with (2 * (i + 1) - 1) in * by lia.
    Exists (app outl2 (cons (Znth i l 0) nil)).
    split_pure_spatial.
    - cancel (IntArray.full numbers_pre numbers_size_pre l).
      cancel (IntArray.seg out_pre 0 (2 * (i + 1) - 1) (app outl2 (cons (Znth i l 0) nil))).
      cancel (IntArray.undef_seg out_pre (2 * (i + 1) - 1) (2 * numbers_size_pre - 1)).
    - split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_p005_intersperse_return_wit_1 : p005_intersperse_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = numbers_size_pre) by lia.
  subst i.
  rewrite IntArray.undef_seg_empty.
  prop_apply (IntArray.seg_Zlength out_pre 0 (2 * numbers_size_pre - 1) outl_2).
  Intros_p Hlen.
  sep_apply (IntArray.seg_to_full out_pre 0 (2 * numbers_size_pre - 1) outl_2).
  replace (out_pre + 0 * sizeof (INT)) with out_pre by lia.
  replace (2 * numbers_size_pre - 1 - 0) with (2 * numbers_size_pre - 1) by lia.
  Exists outl_2.
  split_pure_spatial.
  - cancel (IntArray.full numbers_pre numbers_size_pre l).
    cancel (IntArray.full out_pre (2 * numbers_size_pre - 1) outl_2).
  - split_pures; dump_pre_spatial; lia.
Qed.


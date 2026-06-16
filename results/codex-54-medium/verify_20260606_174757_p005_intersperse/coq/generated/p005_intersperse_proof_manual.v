Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260606_174757_p005_intersperse Require Import p005_intersperse_goal.
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
  sep_apply (IntArray.seg_single out_pre 0 (Znth 0 l BinNums.Z0)).
  rewrite (IntArray.seg_empty out_pre 1 1).
  entailer!.
Qed.

Lemma proof_of_p005_intersperse_entail_wit_2 : p005_intersperse_entail_wit_2.
Proof.
  pre_process.
  Exists nil.
  subst k.
  entailer!.
Qed.

Lemma proof_of_p005_intersperse_entail_wit_3 : p005_intersperse_entail_wit_3.
Proof.
  pre_process.
  Exists (app (app outl_2 (cons delimeter_pre nil)) (cons (Znth i l BinNums.Z0) nil)).
  entailer!.
  rewrite !Zlength_app.
  rewrite !Zlength_cons.
  rewrite !Zlength_nil.
  simpl.
  lia.
Qed.

Lemma proof_of_p005_intersperse_return_wit_1 : p005_intersperse_return_wit_1.
Proof.
  pre_process.
  assert (i = numbers_size_pre) by lia.
  subst i.
  assert (k = (2 * numbers_size_pre) - 1) by lia.
  subst k.
  Exists (app (cons (Znth 0 l BinNums.Z0) nil) outl_2).
  rewrite (IntArray.undef_seg_empty out_pre ((2 * numbers_size_pre) - 1)).
  sep_apply (IntArray.seg_merge_to_full out_pre 0 1 ((2 * numbers_size_pre) - 1)
    (cons (Znth 0 l BinNums.Z0) nil) outl_2); try lia.
  entailer!.
  - replace (out_pre + 0 * sizeof(INT)) with out_pre by lia.
    replace ((2 * numbers_size_pre) - 1 - 0) with ((2 * numbers_size_pre) - 1) by lia.
    cancel (IntArray.full out_pre ((2 * numbers_size_pre) - 1) ((Znth 0 l 0 :: nil) ++ outl_2)).
  - rewrite Zlength_app.
    rewrite Zlength_cons.
    rewrite Zlength_nil.
    lia.
Qed.

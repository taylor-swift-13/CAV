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
From SimpleC.EE.CAV.verify_20260603_181352v_xizi_fifo_timeslice_init Require Import xizi_fifo_timeslice_init_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_xizi_fifo_timeslice_init_return_wit_1 : xizi_fifo_timeslice_init_return_wit_1.
Proof.
  pre_process.
  Exists (replace_Znth 1 0 (replace_Znth 0 0 l)).
  entailer!.
  - rewrite Znth_replace_Znth_Same.
    auto.
    rewrite Zlength_replace_Znth.
    lia.
  - rewrite Znth_replace_Znth_Diff.
    2: rewrite Zlength_replace_Znth; lia.
    2: rewrite Zlength_replace_Znth; lia.
    2: lia.
    rewrite Znth_replace_Znth_Same.
    auto.
    lia.
  - rewrite Zlength_replace_Znth.
    rewrite Zlength_replace_Znth.
    exact H.
Qed.

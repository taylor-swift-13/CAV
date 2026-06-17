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
From SimpleC.EE.CAV.verify_20260603_183100v_xizi_rr_timeslice_init Require Import xizi_rr_timeslice_init_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_xizi_rr_timeslice_init_return_wit_1 : xizi_rr_timeslice_init_return_wit_1.
Proof.
  pre_process.
  Exists (replace_Znth 1 10 (replace_Znth 0 10 l)).
  entailer!.
  + rewrite (Znth_replace_Znth_Same 0 (replace_Znth 0 10 l) 1 10)
      by (rewrite ?Zlength_replace_Znth in *; lia).
    lia.
  + rewrite (Znth_replace_Znth_Diff 0 (replace_Znth 0 10 l) 1 0 10)
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_Same 0 l 0 10) by lia.
    lia.
  + repeat rewrite Zlength_replace_Znth in *.
    lia.
Qed.

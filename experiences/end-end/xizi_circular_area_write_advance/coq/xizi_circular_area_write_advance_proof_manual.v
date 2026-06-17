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
From SimpleC.EE.CAV.verify_20260602_185301v_xizi_circular_area_write_advance Require Import xizi_circular_area_write_advance_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_xizi_circular_area_write_advance_return_wit_2 : xizi_circular_area_write_advance_return_wit_2.
Proof.
  pre_process.
  entailer!.
  - intros Heq.
    rewrite Heq.
    apply Z.rem_same.
    lia.
  - intros Hlt.
    apply Z.rem_small.
    lia.
Qed.

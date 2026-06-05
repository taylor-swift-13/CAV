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
From SimpleC.EE.CAV.verify_20260602_194026v_xizi_circular_area_read_advance Require Import xizi_circular_area_read_advance_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_xizi_circular_area_read_advance_return_wit_1 : xizi_circular_area_read_advance_return_wit_1.
Proof.
  pre_process.
  replace (data_length_pre - (area_length_pre - readidx_pre))
    with (readidx_pre + data_length_pre - area_length_pre) by lia.
  entailer!.
  eapply (Z.rem_unique
            (readidx_pre + data_length_pre)
            area_length_pre
            1
            (readidx_pre + data_length_pre - area_length_pre)).
  lia.
  lia.
  lia.
Qed.

Lemma proof_of_xizi_circular_area_read_advance_return_wit_2 : xizi_circular_area_read_advance_return_wit_2.
Proof.
  pre_process.
  assert (0 <= readidx_pre + data_length_pre) by lia.
  pose proof (Z.rem_bound_pos (readidx_pre + data_length_pre) area_length_pre H6 H0) as Hmod.
  entailer!.
  all: lia.
Qed.

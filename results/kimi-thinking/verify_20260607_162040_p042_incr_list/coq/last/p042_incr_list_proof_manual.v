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
From SimpleC.EE.CAV.verify_20260607_162040_p042_incr_list Require Import p042_incr_list_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p042_incr_list.
Local Open Scope sac.

Lemma proof_of_p042_incr_list_safety_wit_3 : p042_incr_list_safety_wit_3.
Proof.
  pre_process.
  split_pures; dump_pre_spatial.
  assert (Hrange : list_incr_int_range input_l) by eassumption.
  assert (Hi : 0 <= i < Zlength input_l) by lia.
  apply Hrange in Hi.
  lia.
Qed.

Lemma proof_of_p042_incr_list_entail_wit_1 : p042_incr_list_entail_wit_1.
Proof.
  pre_process.
  Exists (nil : list Z).
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. rewrite Zlength_nil. reflexivity.
    + dump_pre_spatial. unfold map_incr. simpl. reflexivity.
    + cancel.
      sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval_2 l_size_pre).
      cancel.
Qed.

Lemma proof_of_p042_incr_list_entail_wit_2 : p042_incr_list_entail_wit_2.
Proof.
  pre_process.
  Exists (app output_prefix_2 (cons (Znth i input_l 0 + 1) nil)).
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. lia.
    + dump_pre_spatial.
      unfold map_incr.
      rewrite sublist_split with (i := 0) (j := i + 1) (k := i) by lia.
      rewrite sublist_single with (i := i) by lia.
      rewrite map_app.
      rewrite H0.
      reflexivity.
    + cancel.
Qed.

Lemma proof_of_p042_incr_list_return_wit_1 : p042_incr_list_return_wit_1.
Proof.
  pre_process.
  assert (Heqi : i = l_size_pre) by lia.
  subst i.
  Exists output_prefix output_prefix l_size_pre.
  split_pure_spatial.
  - cancel.
    sep_apply_l_atomic (IntArray.seg_to_full data_2 0 l_size_pre output_prefix).
    replace (data_2 + 0 * sizeof(INT)) with data_2 by lia.
    replace (l_size_pre - 0) with l_size_pre by lia.
    cancel.
    rewrite IntArray.undef_seg_empty.
    cancel.
  - split_pures.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial.
      rewrite sublist_self by lia. assumption.
    + dump_pre_spatial.
      unfold problem_42_spec.
      split.
      * rewrite H0. reflexivity.
      * intros j Hj.
        unfold map_incr in H0.
        rewrite <- H0.
        rewrite Znth_map by lia.
        reflexivity.
Qed.

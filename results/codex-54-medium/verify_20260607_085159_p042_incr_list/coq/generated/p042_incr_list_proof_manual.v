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
From SimpleC.EE.humaneval Require Import p042_incr_list_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p042_incr_list.
Local Open Scope sac.

Lemma proof_of_p042_incr_list_which_implies_wit_1 : p042_incr_list_which_implies_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.full_split_to_missing_i l_pre i l_size_pre input_l 0).
    + dump_pre_spatial.
      lia.
    + cancel (IntArray.missing_i l_pre i 0 l_size_pre input_l).
      cancel.
  - split_pures; try (dump_pre_spatial; lia); try (dump_pre_spatial; auto).
Qed.

Lemma proof_of_p042_incr_list_entail_wit_1 : p042_incr_list_entail_wit_1.
Proof.
  pre_process.
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval_2 l_size_pre).
  change (map_incr (sublist 0 0 input_l)) with (@nil Z).
  rewrite (IntArray.seg_empty retval_2 0 0).
  split_pure_spatial.
  - cancel (IntArray.undef_seg retval_2 0 l_size_pre).
    cancel (IntArray.full l_pre l_size_pre input_l).
    cancel ((&((retval) # "<anonymous struct>" ->ₛ "data")) # Ptr |-> retval_2).
    cancel ((&((retval) # "<anonymous struct>" ->ₛ "size")) # Int |-> l_size_pre).
  - split_pures; try (dump_pre_spatial; lia); try (dump_pre_spatial; auto).
Qed.

Lemma proof_of_p042_incr_list_entail_wit_2 : p042_incr_list_entail_wit_2.
Proof.
  pre_process.
  replace (map_incr (sublist 0 (i + 1) input_l))
    with (map_incr (sublist 0 i input_l) ++ (Znth i input_l 0 + 1) :: nil).
  2: {
    unfold map_incr.
    rewrite (sublist_split 0 (i + 1) i input_l) by lia.
    rewrite map_app.
    rewrite (sublist_single 0 i input_l) by lia.
    simpl.
    reflexivity.
  }
  rewrite replace_Znth_Znth by lia.
  split_pure_spatial.
  - cancel (IntArray.seg data_v 0 (i + 1)
      (map (fun x : Z => x + 1) (sublist 0 i input_l) ++ (Znth i input_l 0 + 1) :: nil)).
    cancel (IntArray.undef_seg data_v (i + 1) l_size_pre).
    cancel (IntArray.full l_pre l_size_pre input_l).
    cancel ((&((out_v) # "<anonymous struct>" ->ₛ "data")) # Ptr |-> data_v).
    cancel ((&((out_v) # "<anonymous struct>" ->ₛ "size")) # Int |-> l_size_pre).
  - split_pures; try (dump_pre_spatial; lia); try (dump_pre_spatial; auto).
Qed.

Lemma proof_of_p042_incr_list_return_wit_1 : p042_incr_list_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = l_size_pre) by lia.
  subst i.
  Exists (map_incr input_l) l_size_pre data_v.
  assert (HlenZ : Zlength input_l = l_size_pre) by lia.
  rewrite (sublist_self input_l l_size_pre) by exact (eq_sym HlenZ).
  rewrite IntArray.undef_seg_empty.
  sep_apply (IntArray.seg_to_full data_v 0 l_size_pre (map_incr input_l)).
  replace (data_v + 0 * sizeof (INT)) with data_v by lia.
  split_pure_spatial.
  - replace (l_size_pre - 0) with l_size_pre by lia.
    cancel (IntArray.full l_pre l_size_pre input_l).
    cancel (IntArray.full data_v l_size_pre (map_incr input_l)).
    cancel ((&((out_v) # "<anonymous struct>" ->ₛ "data")) # Ptr |-> data_v).
    cancel ((&((out_v) # "<anonymous struct>" ->ₛ "size")) # Int |-> l_size_pre).
  - split_pures;
      try (dump_pre_spatial; lia);
      try (dump_pre_spatial; auto);
      try reflexivity;
      try (rewrite H4; unfold map_incr; rewrite !Zlength_correct; rewrite length_map; reflexivity).
    unfold problem_42_spec, map_incr.
    split.
    * rewrite !Zlength_correct.
      rewrite length_map.
      reflexivity.
    * intros j Hj.
      assert (Hj_nat : (Z.to_nat j < length input_l)%nat).
      { unfold map_incr in Hj.
        rewrite Zlength_correct in Hj.
        rewrite length_map in Hj.
        lia. }
      unfold Znth, map_incr.
      change 0 with ((fun x : Z => x + 1) (-1)).
      rewrite map_nth.
      rewrite (@nth_indep Z input_l (Z.to_nat j) (-1) 0) by exact Hj_nat.
      simpl.
      reflexivity.
Qed.

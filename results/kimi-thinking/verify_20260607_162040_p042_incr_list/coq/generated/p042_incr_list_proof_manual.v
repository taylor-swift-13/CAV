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
  all: assert (Hbounds : 0 <= i < Zlength input_l) by lia.
  all: match goal with
       | H : list_incr_int_range _ |- _ => pose proof (H i Hbounds) as Hrange
       end.
  all: destruct Hrange as [Hlo Hhi].
  all: lia.
Qed.

Lemma proof_of_p042_incr_list_entail_wit_1 : p042_incr_list_entail_wit_1.
Proof.
  pre_process.
  Exists (nil : list Z).
  split_pure_spatial.
  { sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval_2 l_size_pre).
    rewrite IntArray.seg_empty.
    entailer!. }
  { split_pures.
    all: try (dump_pre_spatial; reflexivity).
    all: try (dump_pre_spatial; lia).
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; rewrite Zlength_nil; reflexivity).
    all: try (dump_pre_spatial; unfold map_incr; simpl; reflexivity).
    all: try cancel. }
Qed.

Lemma proof_of_p042_incr_list_entail_wit_2 : p042_incr_list_entail_wit_2.
Proof.
  pre_process.
  Exists (app output_prefix_2 (cons (Znth i input_l 0 + 1) nil)).
  split_pure_spatial.
  { entailer!. }
  { split_pures.
    all: try (dump_pre_spatial; reflexivity).
    all: try (dump_pre_spatial; lia).
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    dump_pre_spatial.
    unfold map_incr.
    rewrite (sublist_split 0 (i + 1) i input_l) by lia.
    rewrite (sublist_single 0 i input_l) by lia.
    rewrite map_app.
    simpl.
    subst output_prefix_2.
    reflexivity. }
Qed.

Lemma Zlength_map_incr : forall l, Zlength (map_incr l) = Zlength l.
Proof.
  intros. unfold map_incr. rewrite !Zlength_correct. rewrite length_map. reflexivity.
Qed.

Lemma Znth_map_incr : forall j l, 0 <= j < Zlength l -> Znth j (map_incr l) 0 = Znth j l 0 + 1.
Proof.
  intros j l. revert j. unfold map_incr.
  induction l as [|a l IH]; intros j H.
  - rewrite Zlength_correct in H. simpl in H. lia.
  - destruct (Z.eq_dec j 0).
    + subst. simpl. reflexivity.
    + assert (Hj' : 0 <= j - 1 < Zlength l) by (rewrite !Zlength_correct in *; simpl in H; lia).
      specialize (IH (j - 1) Hj').
      simpl.
      rewrite !Znth_cons by lia.
      exact IH.
Qed.

Lemma proof_of_p042_incr_list_return_wit_1 : p042_incr_list_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = l_size_pre) by lia.
  match goal with | H : Zlength output_prefix = i |- _ => clear H end.
  subst i.
  match goal with | H : output_prefix = map_incr (sublist _ _ _) |- _ => rename H into Hmap end.
  assert (Hsub : sublist 0 l_size_pre input_l = input_l) by (apply sublist_self; exact H2).
  rewrite Hsub in *.
  Exists output_prefix l_size_pre data_2.
  rewrite IntArray.undef_seg_empty.
  sep_apply (IntArray.seg_to_full data_2 0 l_size_pre output_prefix).
  replace (data_2 + 0 * sizeof(INT)) with data_2 by lia.
  replace (l_size_pre - 0) with l_size_pre by lia.
  split_pure_spatial.
  - entailer!.
  - split_pures.
    + dump_pre_spatial. assumption.
    + dump_pre_spatial. assumption.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial.
      rewrite Hmap. unfold map_incr. rewrite !Zlength_correct. rewrite length_map.
      rewrite <- Zlength_correct. exact H2.
    + dump_pre_spatial. exact H2.
    + dump_pre_spatial. rewrite Hmap. reflexivity.
    + dump_pre_spatial.
      unfold problem_42_spec.
      split.
      * rewrite Hmap. symmetry. apply Zlength_map_incr.
      * intros j Hj.
        rewrite Hmap in Hj.
        rewrite Hmap.
        rewrite Zlength_map_incr in Hj.
        apply Znth_map_incr.
        exact Hj.
Qed.

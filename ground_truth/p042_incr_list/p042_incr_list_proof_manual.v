Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p042_incr_list Require Import p042_incr_list_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p042_incr_list.
Local Open Scope sac.
Require Import Coq.micromega.Lia.

Local Open Scope list_scope.

(* Proof helpers moved from p042_incr_list.v so public contract files expose definitions only. *)

Lemma map_incr_Zlength :
  forall l, Zlength (map_incr l) = Zlength l.
Proof.
  intros l.
  unfold map_incr.
  rewrite !Zlength_correct.
  rewrite length_map.
  reflexivity.
Qed.
Lemma map_incr_sublist_snoc :
  forall l i,
    0 <= i < Zlength l ->
    map_incr (sublist 0 (i + 1) l) =
      map_incr (sublist 0 i l) ++ [Znth i l 0 + 1].
Proof.
  intros l i Hi.
  unfold map_incr.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single 0 i l) by lia.
  rewrite map_app.
  simpl.
  reflexivity.
Qed.
Lemma problem_42_spec_map_incr :
  forall input, problem_42_spec input (map_incr input).
Proof.
  intros input.
  unfold problem_42_spec, map_incr.
  split.
  - rewrite !Zlength_correct.
    rewrite length_map.
    reflexivity.
  - intros i Hi.
    unfold Znth.
    rewrite map_nth_len with (dy := 0).
    + reflexivity.
    + rewrite <- (Nat2Z.id (length input)).
      pose proof (Z2Nat.inj_lt i (Z.of_nat (length input)) ltac:(lia) ltac:(lia)) as Hlt.
      apply (proj1 Hlt).
      rewrite Zlength_correct in Hi.
      rewrite length_map in Hi.
      lia.
Qed.


Lemma proof_of_p042_incr_list_safety_wit_3 : p042_incr_list_safety_wit_3.
Proof.
  pre_process.
  match goal with
  | H: list_incr_int_range input_l |- _ =>
      pose proof (H i) as Hrange
  end.
  entailer!.
Qed.

Lemma proof_of_p042_incr_list_entail_wit_1 : p042_incr_list_entail_wit_1.
Proof.
  pre_process.
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
Qed.

Lemma proof_of_p042_incr_list_entail_wit_2 : p042_incr_list_entail_wit_2.
Proof.
  pre_process.
  rewrite map_incr_sublist_snoc by (rewrite <- H2; lia).
  entailer!.
Qed.

Lemma proof_of_p042_incr_list_return_wit_1 : p042_incr_list_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = l_size_pre) by lia.
  subst i.
  Exists (map_incr input_l) l_size_pre data_2.
  rewrite sublist_self by exact H2.
  sep_apply (IntArray.seg_to_full data_2 0 l_size_pre).
  replace (data_2 + 0 * sizeof (INT)) with data_2 by lia.
  replace (l_size_pre - 0) with l_size_pre by lia.
  rewrite (IntArray.undef_seg_empty data_2 l_size_pre).
  entailer!.
  - apply problem_42_spec_map_incr.
  - rewrite map_incr_Zlength.
    auto.
Qed.

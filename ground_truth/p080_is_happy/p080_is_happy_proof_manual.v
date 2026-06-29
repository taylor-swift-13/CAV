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
From SimpleC.EE.CAV.ground_truth_p080_is_happy Require Import p080_is_happy_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
From AUXLib Require Import ListLib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Strings.Ascii.
Require Import Arith.
Require Import string_bridge.

Import naive_C_Rules.
Require Import p080_is_happy.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p080_is_happy.v so public contract files expose definitions only. *)

Lemma happy_prefix_2 : forall s,
  happy_prefix 2 s.
Proof.
  unfold happy_prefix.
  intros s k Hk.
  lia.
Qed.
Lemma happy_adjacent_2 : forall s,
  Znth 1 s 0 <> Znth 0 s 0 ->
  happy_adjacent 2 s.
Proof.
  unfold happy_adjacent.
  intros s H.
  replace (2 - 1) with 1 by lia.
  replace (2 - 2) with 0 by lia.
  exact H.
Qed.
Lemma happy_adjacent_step : forall i s,
  Znth i s 0 <> Znth (i - 1) s 0 ->
  happy_adjacent (i + 1) s.
Proof.
  unfold happy_adjacent.
  intros i s H.
  replace (i + 1 - 1) with i by lia.
  replace (i + 1 - 2) with (i - 1) by lia.
  exact H.
Qed.
Lemma happy_prefix_step : forall i s,
  happy_prefix i s ->
  happy_adjacent i s ->
  Znth i s 0 <> Znth (i - 1) s 0 ->
  Znth i s 0 <> Znth (i - 2) s 0 ->
  happy_prefix (i + 1) s.
Proof.
  unfold happy_prefix, happy_window_end.
  intros i s Hprefix Hadj Hprev1 Hprev2 k Hk.
  destruct (Z_lt_ge_dec k i).
  - apply Hprefix. lia.
  - assert (k = i) by lia.
    subst k.
    unfold happy_adjacent in Hadj.
    repeat split; assumption.
Qed.
Lemma problem_80_spec_short : forall s,
  Zlength s < 3 ->
  problem_80_spec s 0.
Proof.
  intros s Hshort.
  unfold problem_80_spec, bool_of.
  change (Z.eqb 0 1) with false.
  left.
  exact Hshort.
Qed.
Lemma problem_80_spec_false_first_pair : forall s,
  3 <= Zlength s ->
  Znth 0 s 0 = Znth 1 s 0 ->
  problem_80_spec s 0.
Proof.
  intros s Hlen Heq.
  unfold problem_80_spec, bool_of.
  change (Z.eqb 0 1) with false.
  right.
  exists 0.
  repeat split; try lia.
  left.
  exact Heq.
Qed.
Lemma problem_80_spec_false_prev1 : forall s i,
  2 <= i ->
  i < Zlength s ->
  Znth i s 0 = Znth (i - 1) s 0 ->
  problem_80_spec s 0.
Proof.
  intros s i Hi Hbound Heq.
  unfold problem_80_spec, bool_of.
  change (Z.eqb 0 1) with false.
  right.
  exists (i - 2).
  repeat split; try lia.
  right.
  right.
  replace (i - 2 + 1) with (i - 1) by lia.
  replace (i - 2 + 2) with i by lia.
  symmetry.
  exact Heq.
Qed.
Lemma problem_80_spec_false_prev2 : forall s i,
  2 <= i ->
  i < Zlength s ->
  Znth i s 0 = Znth (i - 2) s 0 ->
  problem_80_spec s 0.
Proof.
  intros s i Hi Hbound Heq.
  unfold problem_80_spec, bool_of.
  change (Z.eqb 0 1) with false.
  right.
  exists (i - 2).
  repeat split; try lia.
  right.
  left.
  replace (i - 2 + 2) with i by lia.
  symmetry.
  exact Heq.
Qed.
Lemma problem_80_spec_true : forall s i,
  ascii_range s ->
  i >= Zlength s ->
  3 <= Zlength s ->
  happy_prefix i s ->
  problem_80_spec s 1.
Proof.
  intros s i _ Hexit Hlen Hprefix.
  unfold problem_80_spec, bool_of.
  change (Z.eqb 1 1) with true.
  split; [lia |].
  intros j Hj Hbound.
  assert (Hwin : happy_window_end (j + 2) s) by (apply Hprefix; lia).
  unfold happy_window_end in Hwin.
  destruct Hwin as [Hneq32 [Hneq31 Hneq21]].
  repeat split.
  - intro Heq.
    apply Hneq21.
    replace (j + 2 - 1) with (j + 1) by lia.
    replace (j + 2 - 2) with j by lia.
    symmetry.
    exact Heq.
  - intro Heq.
    apply Hneq31.
    replace (j + 2 - 2) with j by lia.
    symmetry.
    exact Heq.
  - intro Heq.
    apply Hneq32.
    replace (j + 2 - 1) with (j + 1) by lia.
    symmetry.
    exact Heq.
Qed.


Lemma proof_of_p080_is_happy_entail_wit_1 : p080_is_happy_entail_wit_1.
Proof.
  unfold p080_is_happy_entail_wit_1.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  subst retval.
  entailer!.
  - apply happy_adjacent_2.
    match goal with
    | H : Znth 0 l 0 <> Znth 1 l 0 |- _ =>
        intro Heq; apply H; symmetry; exact Heq
    end.
  - apply happy_prefix_2.
Qed.

Lemma proof_of_p080_is_happy_entail_wit_2 : p080_is_happy_entail_wit_2.
Proof.
  unfold p080_is_happy_entail_wit_2.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  entailer!.
  - apply happy_adjacent_step.
    match goal with
    | H : Znth i l 0 <> Znth (i - 1) l 0 |- _ => exact H
    end.
  - apply happy_prefix_step.
    + assumption.
    + assumption.
    + match goal with
      | H : Znth i l 0 <> Znth (i - 1) l 0 |- _ => exact H
      end.
    + match goal with
      | H : Znth i l 0 <> Znth (i - 2) l 0 |- _ => exact H
      end.
Qed.

Lemma proof_of_p080_is_happy_return_wit_1 : p080_is_happy_return_wit_1.
Proof.
  unfold p080_is_happy_return_wit_1.
  intros.
  pre_process.
  entailer!.
  apply problem_80_spec_true with (i := i); auto; lia.
Qed.

Lemma proof_of_p080_is_happy_return_wit_2 : p080_is_happy_return_wit_2.
Proof.
  unfold p080_is_happy_return_wit_2.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  entailer!.
  apply problem_80_spec_false_prev2 with (i := i); auto; lia.
Qed.

Lemma proof_of_p080_is_happy_return_wit_3 : p080_is_happy_return_wit_3.
Proof.
  unfold p080_is_happy_return_wit_3.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  entailer!.
  apply problem_80_spec_false_prev1 with (i := i); auto; lia.
Qed.

Lemma proof_of_p080_is_happy_return_wit_4 : p080_is_happy_return_wit_4.
Proof.
  unfold p080_is_happy_return_wit_4.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  subst retval.
  entailer!.
  apply problem_80_spec_false_first_pair; try lia.
Qed.

Lemma proof_of_p080_is_happy_return_wit_5 : p080_is_happy_return_wit_5.
Proof.
  unfold p080_is_happy_return_wit_5.
  intros.
  pre_process.
  subst retval.
  entailer!.
  apply problem_80_spec_short.
  lia.
Qed.

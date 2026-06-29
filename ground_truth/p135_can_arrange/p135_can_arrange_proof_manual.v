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
From SimpleC.EE.CAV.ground_truth_p135_can_arrange Require Import p135_can_arrange_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p135_can_arrange.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p135_can_arrange.v so public contract files expose definitions only. *)

Lemma can_arrange_prefix_init : forall l,
  0 <= Zlength l ->
  can_arrange_prefix 0 l (-1).
Proof.
  intros l Hlen.
  unfold can_arrange_prefix.
  repeat split; try lia.
Qed.
Lemma can_arrange_prefix_keep : forall i l max,
  can_arrange_prefix i l max ->
  0 <= i < Zlength l ->
  ~ can_arrange_hit l i ->
  can_arrange_prefix (i + 1) l max.
Proof.
  intros i l max Hpre Hi Hnot.
  unfold can_arrange_prefix in *.
  destruct Hpre as [Hibound [Hmax [Hmaxhit Hall]]].
  repeat split; try lia; try assumption.
  intros j Hj Hhit.
  assert (j < i \/ j = i) as [Hlt | Heq] by lia.
  - apply Hall; [lia | assumption].
  - subst j. contradiction.
Qed.
Lemma can_arrange_prefix_update : forall i l max,
  can_arrange_prefix i l max ->
  0 <= i < Zlength l ->
  can_arrange_hit l i ->
  can_arrange_prefix (i + 1) l i.
Proof.
  intros i l max Hpre Hi Hhit.
  unfold can_arrange_prefix in *.
  destruct Hpre as [Hibound [_ [_ Hall]]].
  split; [lia |].
  split; [lia |].
  split; [right; exact Hhit |].
  intros j Hj Hjhit.
  assert (j < i \/ j = i) as [Hlt | Heq] by lia.
  - pose proof (Hall j ltac:(lia) Hjhit). lia.
  - lia.
Qed.
Lemma can_arrange_hit_of_cond : forall l i,
  0 <= i < Zlength l ->
  Znth i l 0 <= i ->
  can_arrange_hit l i.
Proof.
  intros l i Hi Hle.
  unfold can_arrange_hit.
  split; lia.
Qed.
Lemma can_arrange_not_hit_of_cond : forall l i,
  0 <= i < Zlength l ->
  Znth i l 0 > i ->
  ~ can_arrange_hit l i.
Proof.
  intros l i Hi Hgt Hhit.
  unfold can_arrange_hit in Hhit.
  lia.
Qed.
Lemma can_arrange_prefix_full_spec : forall l r,
  can_arrange_prefix (Zlength l) l r ->
  problem_135_spec l r.
Proof.
  intros l r Hpre.
  unfold can_arrange_prefix in Hpre.
  destruct Hpre as [Hibound [Hr [Hrhit Hmax]]].
  destruct Hrhit as [Hrneg | Hrhit].
  - left.
    split; [assumption |].
    intros k Hhit.
    unfold can_arrange_hit in Hhit.
    pose proof (Hmax k ltac:(lia) Hhit).
    lia.
  - right.
    exists r.
    split; [reflexivity |].
    split; [assumption |].
    intros j Hhit.
    unfold can_arrange_hit in Hhit.
    pose proof (Hmax j ltac:(lia) Hhit).
    lia.
Qed.


Lemma proof_of_p135_can_arrange_entail_wit_1 : p135_can_arrange_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  apply can_arrange_prefix_init.
  lia.
Qed.

Lemma proof_of_p135_can_arrange_entail_wit_2_1 : p135_can_arrange_entail_wit_2_1.
Proof.
  pre_process.
  entailer!.
  apply can_arrange_prefix_update with (max := max).
  - assumption.
  - lia.
  - apply can_arrange_hit_of_cond; lia.
Qed.

Lemma proof_of_p135_can_arrange_entail_wit_2_2 : p135_can_arrange_entail_wit_2_2.
Proof.
  pre_process.
  entailer!.
  apply can_arrange_prefix_keep.
  - assumption.
  - lia.
  - apply can_arrange_not_hit_of_cond; lia.
Qed.

Lemma proof_of_p135_can_arrange_return_wit_1 : p135_can_arrange_return_wit_1.
Proof.
  pre_process.
  replace i with arr_size_pre in * by lia.
  entailer!.
  apply can_arrange_prefix_full_spec.
  rewrite <- H2.
  assumption.
Qed.

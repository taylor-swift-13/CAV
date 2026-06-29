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
From SimpleC.EE.CAV.ground_truth_p056_correct_bracketing Require Import p056_correct_bracketing_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
From AUXLib Require Import ListLib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import string_bridge.

Import naive_C_Rules.
Require Import p056_correct_bracketing.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p056_correct_bracketing.v so public contract files expose definitions only. *)

Lemma Znth_In_range_56 : forall (l : list Z) k d,
  0 <= k < Zlength l ->
  In (Znth k l d) l.
Proof.
  intros l k d Hk.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hk.
  lia.
Qed.
Lemma angle_level_upto_0 : forall l,
  angle_level_upto 0 l = 0.
Proof.
  intros l.
  unfold angle_level_upto.
  reflexivity.
Qed.
Lemma angle_nonnegative_prefix_0 : forall l,
  angle_nonnegative_prefix 0 l.
Proof.
  unfold angle_nonnegative_prefix.
  intros l k Hk.
  lia.
Qed.
Lemma angle_level_upto_step_open : forall i l,
  0 <= i ->
  Znth i l 0 = 60 ->
  angle_level_upto (i + 1) l = angle_level_upto i l + 1.
Proof.
  intros i l Hi Hx.
  unfold angle_level_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  unfold angle_delta.
  rewrite Hx.
  rewrite Z.eqb_refl.
  reflexivity.
Qed.
Lemma angle_level_upto_step_close : forall i l,
  0 <= i ->
  Znth i l 0 = 62 ->
  angle_level_upto (i + 1) l = angle_level_upto i l - 1.
Proof.
  intros i l Hi Hx.
  unfold angle_level_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  unfold angle_delta.
  rewrite Hx.
  replace (Z.eqb 62 60) with false by reflexivity.
  replace (Z.eqb 62 62) with true by reflexivity.
  lia.
Qed.
Lemma angle_nonnegative_prefix_step : forall i l level,
  angle_nonnegative_prefix i l ->
  angle_level_upto (i + 1) l = level ->
  0 <= level ->
  angle_nonnegative_prefix (i + 1) l.
Proof.
  unfold angle_nonnegative_prefix.
  intros i l level Hprefix Hlevel Hnonneg k Hk.
  destruct (Z_lt_ge_dec k i).
  - apply Hprefix. lia.
  - assert (k = i) by lia.
    subst k.
    rewrite Hlevel.
    lia.
Qed.
Lemma problem_56_pre_char : forall l k,
  problem_56_pre l ->
  0 <= k < Zlength l ->
  Znth k l 0 = 60 \/ Znth k l 0 = 62.
Proof.
  intros l k Hpre Hk.
  unfold problem_56_pre in Hpre.
  rewrite Forall_forall in Hpre.
  apply Hpre.
  apply Znth_In_range_56.
  exact Hk.
Qed.
Lemma problem_56_pre_nonzero : forall l n,
  Zlength l = n ->
  problem_56_pre l ->
  forall k, 0 <= k < n -> Znth k l 0 <> 0.
Proof.
  intros l n Hlen Hpre k Hk.
  destruct (problem_56_pre_char l k Hpre ltac:(lia)); lia.
Qed.
Lemma problem_56_spec_true : forall l,
  angle_level_upto (Zlength l) l = 0 ->
  angle_nonnegative_prefix (Zlength l) l ->
  problem_56_spec l 1.
Proof.
  intros l Hlevel Hprefix.
  unfold problem_56_spec, bool_of, angle_balanced.
  simpl.
  split.
  - intros _. split; assumption.
  - intros _. reflexivity.
Qed.
Lemma problem_56_spec_false_negative : forall l i,
  0 <= i ->
  i < Zlength l ->
  angle_level_upto (i + 1) l < 0 ->
  problem_56_spec l 0.
Proof.
  intros l i Hi Hbound Hneg.
  unfold problem_56_spec, bool_of, angle_balanced.
  simpl.
  split.
  - discriminate.
  - intros [_ Hprefix].
    specialize (Hprefix i ltac:(lia)).
    lia.
Qed.
Lemma problem_56_spec_false_final : forall l level,
  angle_level_upto (Zlength l) l = level ->
  level <> 0 ->
  problem_56_spec l 0.
Proof.
  intros l level Hlevel Hneq.
  unfold problem_56_spec, bool_of, angle_balanced.
  simpl.
  split.
  - discriminate.
  - intros [Hbalanced _].
    rewrite Hlevel in Hbalanced.
    lia.
Qed.


Ltac c56_pre :=
  pre_process;
  repeat rewrite app_Znth1 in * by lia.

Lemma proof_of_p056_correct_bracketing_entail_wit_1 : p056_correct_bracketing_entail_wit_1.
Proof.
  unfold p056_correct_bracketing_entail_wit_1.
  intros.
  c56_pre.
  subst retval.
  rewrite angle_level_upto_0.
  entailer!.
  apply angle_nonnegative_prefix_0.
Qed.

Lemma proof_of_p056_correct_bracketing_entail_wit_2_1 : p056_correct_bracketing_entail_wit_2_1.
Proof.
  unfold p056_correct_bracketing_entail_wit_2_1.
  intros.
  c56_pre.
  match goal with
  | Hpre : problem_56_pre l |- _ =>
      destruct (problem_56_pre_char l i Hpre ltac:(lia)) as [Hopen | Hclose];
      congruence
  end.
Qed.

Lemma proof_of_p056_correct_bracketing_entail_wit_2_2 : p056_correct_bracketing_entail_wit_2_2.
Proof.
  unfold p056_correct_bracketing_entail_wit_2_2.
  intros.
  c56_pre.
  assert (Hstep : angle_level_upto (i + 1) l = level - 1).
  { rewrite angle_level_upto_step_close by lia. lia. }
  entailer!.
  eapply angle_nonnegative_prefix_step; eauto; lia.
Qed.

Lemma proof_of_p056_correct_bracketing_entail_wit_2_3 : p056_correct_bracketing_entail_wit_2_3.
Proof.
  unfold p056_correct_bracketing_entail_wit_2_3.
  intros.
  c56_pre.
  assert (Hstep : angle_level_upto (i + 1) l = level + 1).
  { rewrite angle_level_upto_step_open by lia. lia. }
  entailer!.
  eapply angle_nonnegative_prefix_step; eauto; lia.
Qed.

Lemma proof_of_p056_correct_bracketing_return_wit_1 : p056_correct_bracketing_return_wit_1.
Proof.
  unfold p056_correct_bracketing_return_wit_1.
  intros.
  c56_pre.
  subst level.
  assert (i = len) by lia.
  subst i.
  entailer!; try (eapply problem_56_pre_nonzero; eauto; lia).
  eapply problem_56_spec_true; eauto.
  - match goal with
    | Hlen : Zlength l = len,
      Hlevel : 0 = angle_level_upto len l |- _ =>
        rewrite Hlen; symmetry; exact Hlevel
    end.
  - match goal with
    | Hlen : Zlength l = len,
      Hprefix : angle_nonnegative_prefix len l |- _ =>
        rewrite Hlen; exact Hprefix
    end.
Qed.

Lemma proof_of_p056_correct_bracketing_return_wit_2 : p056_correct_bracketing_return_wit_2.
Proof.
  unfold p056_correct_bracketing_return_wit_2.
  intros.
  c56_pre.
  assert (i = len) by lia.
  subst i.
  assert (Hfinal_level : angle_level_upto (Zlength l) l = level).
  {
    match goal with
    | Hlen : Zlength l = len,
      Hlevel : level = angle_level_upto len l |- _ =>
        rewrite Hlen; symmetry; exact Hlevel
    end.
  }
  entailer!; try (eapply problem_56_pre_nonzero; eauto; lia).
  eapply problem_56_spec_false_final; eauto.
Qed.

Lemma proof_of_p056_correct_bracketing_return_wit_3 : p056_correct_bracketing_return_wit_3.
Proof.
  unfold p056_correct_bracketing_return_wit_3.
  intros.
  c56_pre.
  entailer!; try (eapply problem_56_pre_nonzero; eauto; lia).
  eapply problem_56_spec_false_negative with (i := i); eauto; try lia.
  rewrite angle_level_upto_step_close by lia.
  lia.
Qed.

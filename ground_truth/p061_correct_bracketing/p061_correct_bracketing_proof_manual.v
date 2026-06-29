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
From SimpleC.EE.CAV.ground_truth_p061_correct_bracketing Require Import p061_correct_bracketing_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
From AUXLib Require Import ListLib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import string_bridge.

Import naive_C_Rules.
Require Import p061_correct_bracketing.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p061_correct_bracketing.v so public contract files expose definitions only. *)

Lemma Znth_In_range_61 : forall (l : list Z) k d,
  0 <= k < Zlength l ->
  In (Znth k l d) l.
Proof.
  intros l k d Hk.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hk.
  lia.
Qed.
Lemma paren_level_upto_0 : forall l,
  paren_level_upto 0 l = 0.
Proof.
  intros l.
  unfold paren_level_upto.
  reflexivity.
Qed.
Lemma paren_nonnegative_prefix_0 : forall l,
  paren_nonnegative_prefix 0 l.
Proof.
  unfold paren_nonnegative_prefix.
  intros l k Hk.
  lia.
Qed.
Lemma paren_level_upto_step_open : forall i l,
  0 <= i ->
  Znth i l 0 = 40 ->
  paren_level_upto (i + 1) l = paren_level_upto i l + 1.
Proof.
  intros i l Hi Hx.
  unfold paren_level_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  unfold paren_delta.
  rewrite Hx.
  rewrite Z.eqb_refl.
  reflexivity.
Qed.
Lemma paren_level_upto_step_close : forall i l,
  0 <= i ->
  Znth i l 0 = 41 ->
  paren_level_upto (i + 1) l = paren_level_upto i l - 1.
Proof.
  intros i l Hi Hx.
  unfold paren_level_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  unfold paren_delta.
  rewrite Hx.
  replace (Z.eqb 41 40) with false by reflexivity.
  replace (Z.eqb 41 41) with true by reflexivity.
  lia.
Qed.
Lemma paren_nonnegative_prefix_step : forall i l level,
  paren_nonnegative_prefix i l ->
  paren_level_upto (i + 1) l = level ->
  0 <= level ->
  paren_nonnegative_prefix (i + 1) l.
Proof.
  unfold paren_nonnegative_prefix.
  intros i l level Hprefix Hlevel Hnonneg k Hk.
  destruct (Z_lt_ge_dec k i).
  - apply Hprefix. lia.
  - assert (k = i) by lia.
    subst k.
    rewrite Hlevel.
    lia.
Qed.
Lemma problem_61_pre_char : forall l k,
  problem_61_pre l ->
  0 <= k < Zlength l ->
  Znth k l 0 = 40 \/ Znth k l 0 = 41.
Proof.
  intros l k Hpre Hk.
  unfold problem_61_pre in Hpre.
  rewrite Forall_forall in Hpre.
  apply Hpre.
  apply Znth_In_range_61.
  exact Hk.
Qed.
Lemma problem_61_pre_nonzero : forall l n,
  Zlength l = n ->
  problem_61_pre l ->
  forall k, 0 <= k < n -> Znth k l 0 <> 0.
Proof.
  intros l n Hlen Hpre k Hk.
  destruct (problem_61_pre_char l k Hpre ltac:(lia)); lia.
Qed.
Lemma problem_61_spec_true : forall l,
  paren_level_upto (Zlength l) l = 0 ->
  paren_nonnegative_prefix (Zlength l) l ->
  problem_61_spec l 1.
Proof.
  intros l Hlevel Hprefix.
  unfold problem_61_spec, bool_of, paren_balanced.
  simpl.
  split.
  - intros _. split; assumption.
  - intros _. reflexivity.
Qed.
Lemma problem_61_spec_false_negative : forall l i,
  0 <= i ->
  i < Zlength l ->
  paren_level_upto (i + 1) l < 0 ->
  problem_61_spec l 0.
Proof.
  intros l i Hi Hbound Hneg.
  unfold problem_61_spec, bool_of, paren_balanced.
  simpl.
  split.
  - discriminate.
  - intros [_ Hprefix].
    specialize (Hprefix i ltac:(lia)).
    lia.
Qed.
Lemma problem_61_spec_false_final : forall l level,
  paren_level_upto (Zlength l) l = level ->
  level <> 0 ->
  problem_61_spec l 0.
Proof.
  intros l level Hlevel Hneq.
  unfold problem_61_spec, bool_of, paren_balanced.
  simpl.
  split.
  - discriminate.
  - intros [Hbalanced _].
    rewrite Hlevel in Hbalanced.
    lia.
Qed.


Ltac c61_pre :=
  pre_process;
  repeat rewrite app_Znth1 in * by lia.

Lemma proof_of_p061_correct_bracketing_entail_wit_1 : p061_correct_bracketing_entail_wit_1.
Proof.
  unfold p061_correct_bracketing_entail_wit_1.
  intros.
  c61_pre.
  subst retval.
  rewrite paren_level_upto_0.
  entailer!.
  apply paren_nonnegative_prefix_0.
Qed.

Lemma proof_of_p061_correct_bracketing_entail_wit_2_1 : p061_correct_bracketing_entail_wit_2_1.
Proof.
  unfold p061_correct_bracketing_entail_wit_2_1.
  intros.
  c61_pre.
  match goal with
  | Hpre : problem_61_pre l |- _ =>
      destruct (problem_61_pre_char l i Hpre ltac:(lia)) as [Hopen | Hclose];
      congruence
  end.
Qed.

Lemma proof_of_p061_correct_bracketing_entail_wit_2_2 : p061_correct_bracketing_entail_wit_2_2.
Proof.
  unfold p061_correct_bracketing_entail_wit_2_2.
  intros.
  c61_pre.
  assert (Hstep : paren_level_upto (i + 1) l = level - 1).
  { rewrite paren_level_upto_step_close by lia. lia. }
  entailer!.
  eapply paren_nonnegative_prefix_step; eauto; lia.
Qed.

Lemma proof_of_p061_correct_bracketing_entail_wit_2_3 : p061_correct_bracketing_entail_wit_2_3.
Proof.
  unfold p061_correct_bracketing_entail_wit_2_3.
  intros.
  c61_pre.
  assert (Hstep : paren_level_upto (i + 1) l = level + 1).
  { rewrite paren_level_upto_step_open by lia. lia. }
  entailer!.
  eapply paren_nonnegative_prefix_step; eauto; lia.
Qed.

Lemma proof_of_p061_correct_bracketing_return_wit_1 : p061_correct_bracketing_return_wit_1.
Proof.
  unfold p061_correct_bracketing_return_wit_1.
  intros.
  c61_pre.
  subst level.
  assert (i = len) by lia.
  subst i.
  entailer!; try (eapply problem_61_pre_nonzero; eauto; lia).
  eapply problem_61_spec_true; eauto.
  - match goal with
    | Hlen : Zlength l = len,
      Hlevel : 0 = paren_level_upto len l |- _ =>
        rewrite Hlen; symmetry; exact Hlevel
    end.
  - match goal with
    | Hlen : Zlength l = len,
      Hprefix : paren_nonnegative_prefix len l |- _ =>
        rewrite Hlen; exact Hprefix
    end.
Qed.

Lemma proof_of_p061_correct_bracketing_return_wit_2 : p061_correct_bracketing_return_wit_2.
Proof.
  unfold p061_correct_bracketing_return_wit_2.
  intros.
  c61_pre.
  assert (i = len) by lia.
  subst i.
  assert (Hfinal_level : paren_level_upto (Zlength l) l = level).
  {
    match goal with
    | Hlen : Zlength l = len,
      Hlevel : level = paren_level_upto len l |- _ =>
        rewrite Hlen; symmetry; exact Hlevel
    end.
  }
  entailer!; try (eapply problem_61_pre_nonzero; eauto; lia).
  eapply problem_61_spec_false_final; eauto.
Qed.

Lemma proof_of_p061_correct_bracketing_return_wit_3 : p061_correct_bracketing_return_wit_3.
Proof.
  unfold p061_correct_bracketing_return_wit_3.
  intros.
  c61_pre.
  entailer!; try (eapply problem_61_pre_nonzero; eauto; lia).
  eapply problem_61_spec_false_negative with (i := i); eauto; try lia.
  rewrite paren_level_upto_step_close by lia.
  lia.
Qed.

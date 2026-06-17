Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p132_is_nested Require Import p132_is_nested_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p132_is_nested.
Local Open Scope sac.

Lemma proof_of_p132_is_nested_entail_wit_1 : p132_is_nested_entail_wit_1.
Proof.
  unfold p132_is_nested_entail_wit_1; intros.
  pre_process; subst retval; entailer!.
Qed.

Ltac solve_subseq_step :=
  pre_process; entailer!;
  match goal with
  | |- context[subseq_state_prefix (?i + 1) ?l] =>
      rewrite (subseq_state_prefix_step l i) by lia
  end;
  repeat rewrite app_Znth1 in * by lia;
  match goal with
  | H : ?state = subseq_state_prefix ?i ?l |- _ => rewrite <- H
  end;
  unfold subseq_step;
  repeat match goal with
  | |- context[Z.eqb ?a ?b] =>
      destruct (Z.eqb_spec a b); subst; try lia
  end;
  lia.

Ltac solve_return_prefix :=
  pre_process; entailer!;
  match goal with
  | Hge : ?i >= ?len, Hle : ?i <= ?len |- _ =>
      assert (i = len) by lia; subst i
  end.

Lemma proof_of_p132_is_nested_entail_wit_2_1 : p132_is_nested_entail_wit_2_1.
Proof.
  unfold p132_is_nested_entail_wit_2_1; intros; solve_subseq_step.
Qed.

Lemma proof_of_p132_is_nested_entail_wit_2_2 : p132_is_nested_entail_wit_2_2.
Proof.
  unfold p132_is_nested_entail_wit_2_2; intros; solve_subseq_step.
Qed.

Lemma proof_of_p132_is_nested_entail_wit_2_3 : p132_is_nested_entail_wit_2_3.
Proof.
  unfold p132_is_nested_entail_wit_2_3; intros; solve_subseq_step.
Qed.

Lemma proof_of_p132_is_nested_entail_wit_2_4 : p132_is_nested_entail_wit_2_4.
Proof.
  unfold p132_is_nested_entail_wit_2_4; intros; solve_subseq_step.
Qed.

Lemma proof_of_p132_is_nested_entail_wit_2_5 : p132_is_nested_entail_wit_2_5.
Proof.
  unfold p132_is_nested_entail_wit_2_5; intros; solve_subseq_step.
Qed.

Lemma proof_of_p132_is_nested_entail_wit_2_6 : p132_is_nested_entail_wit_2_6.
Proof.
  unfold p132_is_nested_entail_wit_2_6; intros; solve_subseq_step.
Qed.

Lemma proof_of_p132_is_nested_entail_wit_2_7 : p132_is_nested_entail_wit_2_7.
Proof.
  unfold p132_is_nested_entail_wit_2_7; intros; solve_subseq_step.
Qed.

Lemma proof_of_p132_is_nested_entail_wit_2_8 : p132_is_nested_entail_wit_2_8.
Proof.
  unfold p132_is_nested_entail_wit_2_8; intros; solve_subseq_step.
Qed.

Lemma proof_of_p132_is_nested_entail_wit_2_9 : p132_is_nested_entail_wit_2_9.
Proof.
  unfold p132_is_nested_entail_wit_2_9; intros.
  pre_process; entailer!.
  assert (state = 4) by lia; subst state.
  rewrite (subseq_state_prefix_step l i) by lia.
  repeat rewrite app_Znth1 in * by lia.
  match goal with
  | H : 4 = subseq_state_prefix i l |- _ => rewrite <- H
  | H : subseq_state_prefix i l = 4 |- _ => rewrite H
  end.
  unfold subseq_step; reflexivity.
Qed.

Lemma proof_of_p132_is_nested_return_wit_1 : p132_is_nested_return_wit_1.
Proof.
  unfold p132_is_nested_return_wit_1; intros.
  pre_process.
  assert (Hnot4 : state <> 4) by lia.
  assert (Hfull : state = subseq_state_list 0 l).
  {
    match goal with
    | Hstate : state = subseq_state_prefix ?j l |- _ =>
        rewrite Hstate;
        apply subseq_state_prefix_full;
        lia
    | Hstate : subseq_state_prefix ?j l = state |- _ =>
        rewrite <- Hstate;
        apply subseq_state_prefix_full;
        lia
    end.
  }
  entailer!.
  apply problem_132_spec_false; auto.
  intro Hbad.
  rewrite <- Hfull in Hbad.
  contradiction.
Qed.

Lemma proof_of_p132_is_nested_return_wit_2 : p132_is_nested_return_wit_2.
Proof.
  unfold p132_is_nested_return_wit_2; intros.
  pre_process.
  assert (Hstate4 : state = 4) by lia.
  assert (Hfull : state = subseq_state_list 0 l).
  {
    match goal with
    | Hstate : state = subseq_state_prefix ?j l |- _ =>
        rewrite Hstate;
        apply subseq_state_prefix_full;
        lia
    | Hstate : subseq_state_prefix ?j l = state |- _ =>
        rewrite <- Hstate;
        apply subseq_state_prefix_full;
        lia
    end.
  }
  entailer!.
  apply problem_132_spec_true; auto.
  rewrite <- Hfull.
  exact Hstate4.
Qed.

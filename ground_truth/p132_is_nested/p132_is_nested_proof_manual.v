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
From SimpleC.EE.CAV.ground_truth_p132_is_nested Require Import p132_is_nested_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Import naive_C_Rules.
Require Import p132_is_nested.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p132_is_nested.v so public contract files expose definitions only. *)

Lemma subseq_state_list_app : forall a b st,
  subseq_state_list st (List.app a b) =
  subseq_state_list (subseq_state_list st a) b.
Proof.
  induction a as [| c rest IH]; intros b st; simpl; auto.
Qed.
Lemma firstn_succ_nth_132 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = List.app (firstn n l) [nth n l d].
Proof.
  induction n as [| n IH]; intros l d Hlen.
  - destruct l as [| x xs]; simpl in *; try lia; reflexivity.
  - destruct l as [| x xs]; simpl in *; try lia.
    f_equal.
    apply IH.
    lia.
Qed.
Lemma firstn_succ_Znth_132 : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  List.app (firstn (Z.to_nat i) l) [Znth i l d].
Proof.
  intros l i d Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite (firstn_succ_nth_132 (Z.to_nat i) l d).
  - unfold Znth.
    reflexivity.
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
Qed.
Lemma subseq_state_prefix_step : forall s i,
  0 <= i < Zlength s ->
  subseq_state_prefix (i + 1) s =
  subseq_step (subseq_state_prefix i s) (Znth i s 0).
Proof.
  intros s i Hi.
  unfold subseq_state_prefix.
  rewrite (firstn_succ_Znth_132 s i 0) by exact Hi.
  rewrite subseq_state_list_app.
  reflexivity.
Qed.
Lemma subseq_step_range : forall state c,
  0 <= state <= 4 ->
  0 <= subseq_step state c <= 4.
Proof.
  intros state c Hstate.
  unfold subseq_step.
  repeat match goal with
  | |- context[Z.eqb ?a ?b] => destruct (Z.eqb_spec a b); subst
  end; lia.
Qed.
Lemma subseq_state_list_range : forall l state,
  0 <= state <= 4 ->
  0 <= subseq_state_list state l <= 4.
Proof.
  induction l as [| c rest IH]; intros state Hstate; simpl.
  - exact Hstate.
  - apply IH.
    apply subseq_step_range.
    exact Hstate.
Qed.
Lemma subseq_state_prefix_range : forall s i,
  0 <= subseq_state_prefix i s <= 4.
Proof.
  intros s i.
  unfold subseq_state_prefix.
  apply subseq_state_list_range.
  lia.
Qed.
Lemma subseq_state_prefix_full : forall s i,
  i = Zlength s ->
  subseq_state_prefix i s = subseq_state_list 0 s.
Proof.
  intros s i Hi.
  unfold subseq_state_prefix.
  rewrite Hi.
  rewrite firstn_all2; auto.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  lia.
Qed.
Lemma problem_132_spec_true : forall s,
  subseq_state_list 0 s = 4 ->
  problem_132_spec s 1.
Proof.
  intros s Hstate.
  unfold problem_132_spec, bool_of.
  simpl.
  split; auto.
Qed.
Lemma problem_132_spec_false : forall s,
  subseq_state_list 0 s <> 4 ->
  problem_132_spec s 0.
Proof.
  intros s Hstate.
  unfold problem_132_spec, bool_of.
  simpl.
  split; intro H; try discriminate.
  contradiction.
Qed.


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

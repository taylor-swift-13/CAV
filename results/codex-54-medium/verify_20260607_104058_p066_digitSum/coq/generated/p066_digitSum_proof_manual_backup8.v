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
From output.verify_20260607_104058_p066_digitSum.coq.generated Require Import p066_digitSum_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p066_digitSum.
Local Open Scope sac.

Lemma proof_of_p066_digitSum_safety_wit_5 : p066_digitSum_safety_wit_5.
Proof.
  unfold p066_digitSum_safety_wit_5, derivable1, andp, coq_prop, sepcon.
  intros len l s_pre sum i m H.
  simpl in H.
  repeat match type of H with
  | _ /\ _ => destruct H
  | ex _ => destruct H
  end.
  split; simpl.
  - match goal with
    | Hrange : digit_sum_int_range l,
      Hzlen : Zlength l = len,
      Hsum : sum = sum_upper_upto i l,
      Hige0 : 0 <= i,
      Hilt : i < len |- _ =>
        assert (Hi_lt : i < Zlength l) by (rewrite Hzlen; lia);
        assert (Happ : Znth i (app l (cons 0 nil)) 0 = Znth i l 0).
        { rewrite app_Znth1; [reflexivity | split; lia]. }
        pose proof (Hrange i Hige0 Hi_lt) as Hbounds;
        destruct Hbounds as [_ Hbounds];
        rewrite Happ in *;
        subst sum;
        lia
    end.
  - match goal with
    | Hrange : digit_sum_int_range l,
      Hzlen : Zlength l = len,
      Hsum : sum = sum_upper_upto i l,
      Hige0 : 0 <= i,
      Hilt : i < len |- _ =>
        assert (Hi_lt : i < Zlength l) by (rewrite Hzlen; lia);
        assert (Happ : Znth i (app l (cons 0 nil)) 0 = Znth i l 0).
        { rewrite app_Znth1; [reflexivity | split; lia]. }
        pose proof (Hrange i Hige0 Hi_lt) as Hbounds;
        destruct Hbounds as [_ Hbounds];
        rewrite Happ in *;
        subst sum;
        lia
    end.
Qed.

Lemma proof_of_p066_digitSum_entail_wit_1 : p066_digitSum_entail_wit_1.
Proof.
  unfold p066_digitSum_entail_wit_1, derivable1, andp, coq_prop, sepcon.
  intros s_pre len l retval m H.
  simpl in H.
  repeat match type of H with
  | _ /\ _ => destruct H
  | ex _ => destruct H
  end.
  subst retval.
  split; [|].
  - repeat split; try lia; try assumption.
    unfold sum_upper_upto; simpl; reflexivity.
  - exists x0, x.
    split.
    + eapply join_comm; eauto.
    + split; assumption.
Qed.

Lemma proof_of_p066_digitSum_entail_wit_2_1 : p066_digitSum_entail_wit_2_1.
Proof.
  unfold p066_digitSum_entail_wit_2_1, derivable1, andp, coq_prop, sepcon.
  intros len l s_pre sum i m H.
  simpl in H.
  repeat match type of H with
  | _ /\ _ => destruct H
  | ex _ => destruct H
  end.
  split; [|assumption].
  repeat split; try lia; try assumption.
  match goal with
  | Hzlen : Zlength l = len,
    Hsum : sum = sum_upper_upto i l,
    Hige65 : 65 <= Znth i (app l (cons 0 nil)) 0,
    Hile90 : Znth i (app l (cons 0 nil)) 0 <= 90,
    Hige0 : 0 <= i,
    Hilt : i < len |- _ =>
      assert (Hi_lt : i < Zlength l) by (rewrite Hzlen; lia);
      assert (Happ : Znth i (app l (cons 0 nil)) 0 = Znth i l 0).
      { rewrite app_Znth1; [reflexivity | split; lia]. }
      rewrite Hsum.
      rewrite sum_upper_upto_step_upper by (try exact Hi_lt; rewrite <- Happ; lia).
      rewrite Happ.
      lia
  end.
Qed.

Lemma proof_of_p066_digitSum_entail_wit_2_2 : p066_digitSum_entail_wit_2_2.
Proof.
  unfold p066_digitSum_entail_wit_2_2, derivable1, andp, coq_prop, sepcon.
  intros len l s_pre sum i m H.
  simpl in H.
  repeat match type of H with
  | _ /\ _ => destruct H
  | ex _ => destruct H
  end.
  split; [|assumption].
  repeat split; try lia; try assumption.
  match goal with
  | Hzlen : Zlength l = len,
    Hsum : sum = sum_upper_upto i l,
    Hlt65 : Znth i (app l (cons 0 nil)) 0 < 65,
    Hige0 : 0 <= i,
    Hilt : i < len |- _ =>
      assert (Hi_lt : i < Zlength l) by (rewrite Hzlen; lia);
      assert (Happ : Znth i (app l (cons 0 nil)) 0 = Znth i l 0).
      { rewrite app_Znth1; [reflexivity | split; lia]. }
      rewrite Hsum.
      rewrite sum_upper_upto_step_not_upper by (try exact Hi_lt; rewrite <- Happ; lia).
      lia
  end.
Qed.

Lemma proof_of_p066_digitSum_entail_wit_2_3 : p066_digitSum_entail_wit_2_3.
Proof.
  unfold p066_digitSum_entail_wit_2_3, derivable1, andp, coq_prop, sepcon.
  intros len l s_pre sum i m H.
  simpl in H.
  repeat match type of H with
  | _ /\ _ => destruct H
  | ex _ => destruct H
  end.
  split; [|assumption].
  repeat split; try lia; try assumption.
  match goal with
  | Hzlen : Zlength l = len,
    Hsum : sum = sum_upper_upto i l,
    Hgt90 : Znth i (app l (cons 0 nil)) 0 > 90,
    Hige0 : 0 <= i,
    Hilt : i < len |- _ =>
      assert (Hi_lt : i < Zlength l) by (rewrite Hzlen; lia);
      assert (Happ : Znth i (app l (cons 0 nil)) 0 = Znth i l 0).
      { rewrite app_Znth1; [reflexivity | split; lia]. }
      rewrite Hsum.
      rewrite sum_upper_upto_step_not_upper by (try exact Hi_lt; rewrite <- Happ; lia).
      lia
  end.
Qed.

Lemma proof_of_p066_digitSum_return_wit_1 : p066_digitSum_return_wit_1.
Proof.
  unfold p066_digitSum_return_wit_1, derivable1, andp, coq_prop, sepcon.
  intros len l s_pre sum i m H.
  simpl in H.
  repeat match type of H with
  | _ /\ _ => destruct H
  | ex _ => destruct H
  end.
  split; [|split; assumption].
  - assumption.
  - unfold problem_66_spec.
    match goal with
    | Hsum : sum = sum_upper_upto i l,
      Hige : i >= len,
      Hile : i <= len |- _ =>
        assert (Hi_eq : i = len) by lia;
        subst i;
        rewrite Hsum;
        apply sum_upper_upto_length
    end.
Qed.

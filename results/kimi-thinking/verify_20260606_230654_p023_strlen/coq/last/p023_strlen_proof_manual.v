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
From SimpleC.EE.CAV.verify_20260606_230654_p023_strlen Require Import p023_strlen_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p023_strlen.
Local Open Scope sac.

Lemma proof_of_p023_strlen_entail_wit_2 : p023_strlen_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  - intros k [Hk1 Hk2].
    destruct (Z_lt_ge_dec k i).
    + auto.
    + assert (k = i) by lia.
      subst k.
      assert (i < n).
      {
        destruct (Z_lt_ge_dec i n); [lia |].
        assert (i = n) as -> by lia.
        rewrite app_Znth2 in * by lia.
        replace (n - Zlength l) with 0 in * by lia.
        rewrite Znth0_cons in *.
        contradiction.
      }
      rewrite app_Znth1 in * by lia.
      auto.
  - assert (i < n).
    {
      destruct (Z_lt_ge_dec i n); [lia |].
      assert (i = n) as -> by lia.
      rewrite app_Znth2 in * by lia.
      replace (n - Zlength l) with 0 in * by lia.
      rewrite Znth0_cons in *.
      contradiction.
    }
    lia.
Qed.

Lemma proof_of_p023_strlen_return_wit_1 : p023_strlen_return_wit_1.
Proof.
  pre_process.
  entailer!.
  - assert (i = n).
    {
      destruct (Z_lt_ge_dec i n).
      + rewrite app_Znth1 in * by lia.
        unfold problem_23_pre in *.
        exfalso.
        match goal with
        | H : forall k, _ -> Znth k _ _ <> 0 |- _ =>
            apply (H i); [lia | auto]
        end.
      + lia.
    }
    subst i.
    unfold problem_23_spec.
    lia.
  - assert (i = n).
    {
      destruct (Z_lt_ge_dec i n).
      + rewrite app_Znth1 in * by lia.
        unfold problem_23_pre in *.
        exfalso.
        match goal with
        | H : forall k, _ -> Znth k _ _ <> 0 |- _ =>
            apply (H i); [lia | auto]
        end.
      + lia.
    }
    subst i.
    auto.
  - assert (i = n).
    {
      destruct (Z_lt_ge_dec i n).
      + rewrite app_Znth1 in * by lia.
        unfold problem_23_pre in *.
        exfalso.
        match goal with
        | H : forall k, _ -> Znth k _ _ <> 0 |- _ =>
            apply (H i); [lia | auto]
        end.
      + lia.
    }
    subst i.
    auto.
Qed.

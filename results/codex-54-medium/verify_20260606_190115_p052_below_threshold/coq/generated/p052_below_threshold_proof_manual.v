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
From SimpleC.EE.CAV.verify_20260606_190115_p052_below_threshold Require Import p052_below_threshold_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p052_below_threshold.
Local Open Scope sac.

Lemma proof_of_p052_below_threshold_entail_wit_2 : p052_below_threshold_entail_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full l_pre l_size_pre input_l).
  - split_pures.
    + dump_pre_spatial; try assumption; try lia.
    + dump_pre_spatial; try assumption; try lia.
    + dump_pre_spatial; try assumption; try lia.
    + dump_pre_spatial; try assumption; try lia.
    + hnf; intros m Hm; hnf; intros k Hk.
      assert (k < i \/ k = i) as [Hlt | Heq] by lia.
      * match goal with
        | Hforall : forall k : Z, _ |- _ => apply Hforall; lia
        end.
      * subst k. lia.
Qed.

Lemma proof_of_p052_below_threshold_return_wit_1 : p052_below_threshold_return_wit_1.
Proof.
  pre_process.
  prop_apply IntArray.full_Zlength.
  Intros_p Hlen.
  assert (i = l_size_pre) by lia.
  subst i.
  right.
  entailer!.
  split.
  - hnf; lia.
  - split.
    + hnf.
      unfold problem_52_spec.
      split.
      * intros _. reflexivity.
      * intros _ k Hk.
        match goal with
        | Hforall : forall k : Z, _ |- _ => apply Hforall; rewrite Hlen in Hk; lia
        end.
    + assumption.
Qed.

Lemma proof_of_p052_below_threshold_return_wit_2 : p052_below_threshold_return_wit_2.
Proof.
  pre_process.
  prop_apply IntArray.full_Zlength.
  Intros_p Hlen.
  left.
  entailer!.
  split.
  - hnf; reflexivity.
  - split.
    + hnf.
      unfold problem_52_spec.
      split.
      * intros Hall.
        pose proof (Hall i) as Hi.
        assert (Hrange : 0 <= i < Zlength input_l) by (rewrite Hlen; lia).
        specialize (Hi Hrange).
        lia.
      * intros Hfalse.
        discriminate.
    + assumption.
Qed.

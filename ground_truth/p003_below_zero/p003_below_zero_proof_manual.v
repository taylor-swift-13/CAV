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
From SimpleC.EE Require Import p003_below_zero_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.

Import naive_C_Rules.
Local Open Scope sac.

Lemma sum_sublist_snoc : forall l i,
  0 <= i < Zlength l ->
  sum (sublist 0 i l) + Znth i l 0 = sum (sublist 0 (i + 1) l).
Proof.
  intros l i Hi.
  rewrite (sublist_split 0 (i + 1) i l)
    by (try rewrite <- Zlength_correct; lia).
  rewrite sublist_single with (d := 0) by lia.
  rewrite sum_app. simpl. lia.
Qed.

Lemma proof_of_p003_below_zero_safety_wit_3 : p003_below_zero_safety_wit_3.
Proof.
  pre_process.
  prop_apply IntArray.full_length.
  Intros.
  subst num.
  rewrite sum_sublist_snoc by (rewrite Zlength_correct; lia).
  entailer!.
  all: match goal with
  | H: forall k, 0 <= k /\ k < _ -> _ |- _ =>
      specialize (H i); lia
  end.
Qed.

Lemma proof_of_p003_below_zero_entail_wit_1 : p003_below_zero_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_p003_below_zero_entail_wit_2 : p003_below_zero_entail_wit_2.
Proof.
  pre_process.
  prop_apply IntArray.full_length.
  Intros.
  subst num.
  assert (Hstep: sum (sublist 0 i l) + Znth i l 0 =
                 sum (sublist 0 (i + 1) l)).
  { apply sum_sublist_snoc. rewrite Zlength_correct; lia. }
  entailer!.
  intros k Hk.
  destruct (Z_lt_ge_dec k i).
  - match goal with
    | H: forall k, 0 <= k /\ k < i -> 0 <= sum (sublist 0 (k + 1) l) |- _ =>
        apply H; lia
    end.
  - assert (k = i) by lia.
    subst k.
    rewrite <- Hstep. lia.
Qed.

Lemma proof_of_p003_below_zero_return_wit_1 : p003_below_zero_return_wit_1.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  entailer!.
  intros k Hk.
  match goal with
  | H: forall k, 0 <= k /\ k < i -> 0 <= sum (sublist 0 (k + 1) l) |- _ =>
      apply H; lia
  end.
Qed.

Lemma proof_of_p003_below_zero_return_wit_2 : p003_below_zero_return_wit_2.
Proof.
  pre_process.
  prop_apply IntArray.full_length.
  Intros.
  rewrite <- derivable1_orp_intros2.
  entailer!.
  Exists i.
  entailer!.
  subst num.
  rewrite <- sum_sublist_snoc by (rewrite Zlength_correct; lia).
  lia.
Qed.

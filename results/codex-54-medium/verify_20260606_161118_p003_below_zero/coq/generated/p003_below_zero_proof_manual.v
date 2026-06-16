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
From SimpleC.EE.CAV.verify_20260606_161118_p003_below_zero Require Import p003_below_zero_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p003_below_zero.
Local Open Scope sac.

Lemma proof_of_p003_below_zero_safety_wit_3 : p003_below_zero_safety_wit_3.
Proof.
  pre_process.
  prop_apply IntArray.full_Zlength.
  entailer!.
  - subst num.
    replace (sum (sublist 0 i l) + Znth i l 0)
      with (sum (sublist 0 (i + 1) l)).
    2:{
      rewrite (sublist_split 0 (i + 1) i l) by lia.
      rewrite sum_app.
      rewrite (sublist_single 0 i l) by lia.
      simpl.
      lia.
    }
    match goal with
    | H: forall k : Z, ((0 <= k /\ k < operations_size_pre) -> _) |- _ =>
        specialize (H i)
    end.
    assert (0 <= i /\ i < operations_size_pre) by lia.
    lia.
  - subst num.
    replace (sum (sublist 0 i l) + Znth i l 0)
      with (sum (sublist 0 (i + 1) l)).
    2:{
      rewrite (sublist_split 0 (i + 1) i l) by lia.
      rewrite sum_app.
      rewrite (sublist_single 0 i l) by lia.
      simpl.
      lia.
    }
    match goal with
    | H: forall k : Z, ((0 <= k /\ k < operations_size_pre) -> _) |- _ =>
        specialize (H i)
    end.
    assert (0 <= i /\ i < operations_size_pre) by lia.
    lia.
Qed.

Lemma proof_of_p003_below_zero_entail_wit_1 : p003_below_zero_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_p003_below_zero_entail_wit_2 : p003_below_zero_entail_wit_2.
Proof.
  pre_process.
  prop_apply IntArray.full_Zlength.
  entailer!.
  subst num.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite sum_app.
  rewrite (sublist_single 0 i l) by lia.
  simpl.
  lia.
Qed.

Lemma proof_of_p003_below_zero_entail_wit_3 : p003_below_zero_entail_wit_3.
Proof.
  pre_process.
  prop_apply IntArray.full_Zlength.
  entailer!.
  - intros k Hk.
    destruct (Z_lt_ge_dec k i).
    + match goal with
      | H: forall k_2 : Z, ((0 <= k_2 /\ k_2 < i) -> _) |- _ => apply H
      end.
      lia.
    + assert (k = i) by lia.
      subst k.
      replace (sum (sublist 0 (i + 1) l))
        with (sum (sublist 0 i l) + Znth i l 0).
      2:{
        rewrite (sublist_split 0 (i + 1) i l) by lia.
        rewrite sum_app.
        rewrite (sublist_single 0 i l) by lia.
        simpl.
        lia.
      }
      subst num.
      lia.
  - subst num.
    rewrite (sublist_split 0 (i + 1) i l) by lia.
    rewrite sum_app.
    rewrite (sublist_single 0 i l) by lia.
    simpl.
    lia.
Qed.

Lemma proof_of_p003_below_zero_entail_wit_4 : p003_below_zero_entail_wit_4.
Proof.
  pre_process.
  entailer!.
  replace i with operations_size_pre in * by lia.
  match goal with
  | H: forall k_3 : Z, ((0 <= k_3 /\ k_3 < operations_size_pre) -> _) |- _ => apply H
  end.
Qed.

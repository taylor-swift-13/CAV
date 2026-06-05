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
From SimpleC.EE.CAV.verify_20260605_041101v_aug_string_count_index_004 Require Import aug_string_count_index_004_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import aug_string_count_index_004.
Local Open Scope sac.

Lemma aug_string_count_index_004_spec_app_single :
  forall (l : list Z) (x : Z),
    aug_string_count_index_004_spec (l ++ x :: nil) =
    aug_string_count_index_004_spec l + (if Z.eq_dec x 101 then 1 else 0).
Proof.
  induction l; intros x.
  - simpl. destruct (Z.eq_dec x 101); lia.
  - simpl.
    destruct (Z.eq_dec a 101);
      rewrite IHl;
      destruct (Z.eq_dec x 101);
      lia.
Qed.

Lemma proof_of_aug_string_count_index_004_entail_wit_1 : aug_string_count_index_004_entail_wit_1.
Proof.
  unfold aug_string_count_index_004_entail_wit_1.
  intros.
  Exists nil.
  Exists l.
  entailer!.
Qed.

Lemma proof_of_aug_string_count_index_004_entail_wit_2_1 : aug_string_count_index_004_entail_wit_2_1.
Proof.
  unfold aug_string_count_index_004_entail_wit_2_1.
  pre_process.
  assert (Hi_lt_n : i < n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - exact Hlt.
    - assert (Hi_eq : i = n) by lia.
      rewrite Hi_eq in H0.
      rewrite app_Znth2 in H0 by lia.
      replace (n - Zlength l) with 0 in H0 by lia.
      simpl in H0.
      exfalso.
      apply H0.
      reflexivity.
  }
  subst l.
  destruct l2_2.
  - rewrite app_nil_r in H0.
    rewrite app_Znth2 in H0 by lia.
    replace (i - Zlength l1_2) with 0 in H0 by lia.
    simpl in H0.
    exfalso.
    apply H0.
    reflexivity.
  - rename z into x.
    rename l2_2 into xs.
    assert (Hx_eq : x = 101).
    {
      rewrite <- app_assoc in H.
      rewrite app_Znth2 in H by lia.
      replace (i - Zlength l1_2) with 0 in H by lia.
      simpl in H.
      change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H.
      lia.
    }
    assert (Hspec_next :
      count + 1 = aug_string_count_index_004_spec (l1_2 ++ x :: nil)).
    {
      subst count.
      rewrite aug_string_count_index_004_spec_app_single.
      destruct (Z.eq_dec x 101); lia.
    }
    assert (Happ : l1_2 ++ x :: xs = (l1_2 ++ x :: nil) ++ xs).
    {
      rewrite <- app_assoc.
      reflexivity.
    }
    assert (Hlen_prefix : Zlength (l1_2 ++ x :: nil) = i + 1).
    {
      rewrite Zlength_app_cons.
      lia.
    }
    Exists (l1_2 ++ x :: nil).
    Exists xs.
    entailer!.
Qed.

Lemma proof_of_aug_string_count_index_004_entail_wit_2_2 : aug_string_count_index_004_entail_wit_2_2.
Proof.
  unfold aug_string_count_index_004_entail_wit_2_2.
  pre_process.
  assert (Hi_lt_n : i < n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - exact Hlt.
    - assert (Hi_eq : i = n) by lia.
      rewrite Hi_eq in H0.
      rewrite app_Znth2 in H0 by lia.
      replace (n - Zlength l) with 0 in H0 by lia.
      simpl in H0.
      exfalso.
      apply H0.
      reflexivity.
  }
  subst l.
  destruct l2_2.
  - rewrite app_nil_r in H0.
    rewrite app_Znth2 in H0 by lia.
    replace (i - Zlength l1_2) with 0 in H0 by lia.
    simpl in H0.
    exfalso.
    apply H0.
    reflexivity.
  - rename z into x.
    rename l2_2 into xs.
    assert (Hx_ne : x <> 101).
    {
      rewrite <- app_assoc in H.
      rewrite app_Znth2 in H by lia.
      replace (i - Zlength l1_2) with 0 in H by lia.
      simpl in H.
      change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H.
      exact H.
    }
    assert (Hspec_next :
      count = aug_string_count_index_004_spec (l1_2 ++ x :: nil)).
    {
      subst count.
      rewrite aug_string_count_index_004_spec_app_single.
      destruct (Z.eq_dec x 101); lia.
    }
    assert (Happ : l1_2 ++ x :: xs = (l1_2 ++ x :: nil) ++ xs).
    {
      rewrite <- app_assoc.
      reflexivity.
    }
    assert (Hlen_prefix : Zlength (l1_2 ++ x :: nil) = i + 1).
    {
      rewrite Zlength_app_cons.
      lia.
    }
    Exists (l1_2 ++ x :: nil).
    Exists xs.
    entailer!.
Qed.

Lemma proof_of_aug_string_count_index_004_entail_wit_3 : aug_string_count_index_004_entail_wit_3.
Proof.
  unfold aug_string_count_index_004_entail_wit_3.
  pre_process.
  assert (Hi_eq_n : i = n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - assert (Znth i l 0 <> 0).
      {
        match goal with
        | Hnz : forall k : Z, 0 <= k < n -> Znth k l 0 <> 0 |- _ =>
            apply Hnz; lia
        end.
      }
      match goal with
      | Hzero : Znth i (l ++ 0 :: nil) 0 = 0 |- _ =>
          rewrite app_Znth1 in Hzero by lia;
          contradiction
      end.
    - lia.
  }
  subst i.
  assert (Hl2_nil : l2_2 = nil).
  {
    destruct l2_2 as [| x xs].
    - reflexivity.
    - exfalso.
      match goal with
      | Hshape : l = app l1_2 (x :: xs),
        Hlen1 : Zlength l1_2 = n,
        Hlen : Zlength l = n |- _ =>
          rewrite Hshape in Hlen;
          rewrite Zlength_app, Zlength_cons in Hlen;
          pose proof Zlength_nonneg xs;
          lia
      end.
  }
  subst l2_2.
  assert (Hl1_eq_l : l1_2 = l).
  {
    match goal with
    | Hshape : l = app l1_2 nil |- _ =>
        rewrite app_nil_r in Hshape;
        symmetry;
        exact Hshape
    end.
  }
  assert (Hspec_full : count = aug_string_count_index_004_spec l).
  {
    subst count.
    rewrite Hl1_eq_l.
    reflexivity.
  }
  replace (Zlength l1_2) with n by lia.
  Exists l.
  Exists nil.
  entailer!; try rewrite app_nil_r; try reflexivity.
Qed.

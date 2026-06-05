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
From SimpleC.EE.CAV.verify_20260605_010426v_array_sum_nonnegative Require Import array_sum_nonnegative_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_sum_nonnegative.
Local Open Scope sac.

Lemma array_sum_nonnegative_spec_app_single :
  forall (l : list Z) (x : Z),
    array_sum_nonnegative_spec (l ++ x :: nil) =
    array_sum_nonnegative_spec l + (if Z_le_dec 0 x then x else 0).
Proof.
  induction l; intros x.
  - simpl. destruct (Z_le_dec 0 x); lia.
  - simpl.
    destruct (Z_le_dec 0 a);
      rewrite IHl;
      destruct (Z_le_dec 0 x);
      lia.
Qed.

Lemma array_sum_nonnegative_spec_app :
  forall (l1 l2 : list Z),
    array_sum_nonnegative_spec (l1 ++ l2) =
    array_sum_nonnegative_spec l1 + array_sum_nonnegative_spec l2.
Proof.
  induction l1; intros l2.
  - simpl. lia.
  - simpl.
    destruct (Z_le_dec 0 a); rewrite IHl1; lia.
Qed.

Lemma array_sum_nonnegative_spec_nonneg :
  forall (l : list Z),
    0 <= array_sum_nonnegative_spec l.
Proof.
  induction l.
  - simpl. lia.
  - simpl. destruct (Z_le_dec 0 a); lia.
Qed.

Lemma array_sum_nonnegative_spec_prefix_le :
  forall (l : list Z) (i : Z),
    0 <= i <= Zlength l ->
    array_sum_nonnegative_spec (sublist 0 i l) <= array_sum_nonnegative_spec l.
Proof.
  intros l i Hi.
  pose proof Hi as Hi'.
  destruct Hi as [Hlo Hhi].
  replace l with (sublist 0 (Zlength l) l) at 2.
  2:{ rewrite sublist_self; reflexivity. }
  rewrite (sublist_split 0 (Zlength l) i l) by lia.
  rewrite array_sum_nonnegative_spec_app.
  pose proof (array_sum_nonnegative_spec_nonneg (sublist i (Zlength l) l)).
  lia.
Qed.

Lemma proof_of_array_sum_nonnegative_safety_wit_4 : array_sum_nonnegative_safety_wit_4.
Proof.
  unfold array_sum_nonnegative_safety_wit_4.
  pre_process.
  assert (Hprefix :
    array_sum_nonnegative_spec (sublist 0 (i + 1) l) =
    sum + Znth i l 0).
  {
    subst sum.
    rewrite (sublist_split 0 (i + 1) i l) by lia.
    rewrite (sublist_single 0 i l) by lia.
    rewrite array_sum_nonnegative_spec_app_single.
    destruct (Z_le_dec 0 (Znth i l 0)); lia.
  }
  pose proof (array_sum_nonnegative_spec_prefix_le l (i + 1)) as Hle.
  assert (Hrange : 0 <= i + 1 <= Zlength l) by lia.
  specialize (Hle Hrange).
  rewrite Hprefix in Hle.
  entailer!.
Qed. 

Lemma proof_of_array_sum_nonnegative_entail_wit_1 : array_sum_nonnegative_entail_wit_1.
Proof.
  unfold array_sum_nonnegative_entail_wit_1.
  intros.
  entailer!.
Qed. 

Lemma proof_of_array_sum_nonnegative_entail_wit_2_1 : array_sum_nonnegative_entail_wit_2_1.
Proof.
  unfold array_sum_nonnegative_entail_wit_2_1.
  intros.
  entailer!.
  - assert (Hprefix :
      array_sum_nonnegative_spec (sublist 0 (i + 1) l) =
      sum + Znth i l 0).
    {
      subst sum.
      rewrite (sublist_split 0 (i + 1) i l) by lia.
      rewrite (sublist_single 0 i l) by lia.
      rewrite array_sum_nonnegative_spec_app_single.
      destruct (Z_le_dec 0 (Znth i l 0)); lia.
    }
    pose proof (array_sum_nonnegative_spec_prefix_le l (i + 1)) as Hle.
    assert (Hrange : 0 <= i + 1 <= Zlength l) by lia.
    specialize (Hle Hrange).
    rewrite Hprefix in Hle.
    lia.
  - subst sum.
    rewrite (sublist_split 0 (i + 1) i l) by lia.
    rewrite (sublist_single 0 i l) by lia.
    rewrite array_sum_nonnegative_spec_app_single.
    destruct (Z_le_dec 0 (Znth i l 0)); lia.
Qed. 

Lemma proof_of_array_sum_nonnegative_entail_wit_2_2 : array_sum_nonnegative_entail_wit_2_2.
Proof.
  unfold array_sum_nonnegative_entail_wit_2_2.
  intros.
  entailer!.
  subst sum.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single 0 i l) by lia.
  rewrite array_sum_nonnegative_spec_app_single.
  destruct (Z_le_dec 0 (Znth i l 0)); lia.
Qed. 

Lemma proof_of_array_sum_nonnegative_return_wit_1 : array_sum_nonnegative_return_wit_1.
Proof.
  unfold array_sum_nonnegative_return_wit_1.
  intros.
  entailer!.
  assert (i = n_pre) by lia.
  subst i.
  match goal with
  | Hsum : sum = _ |- _ => rewrite Hsum
  end.
  match goal with
  | Hlen : Zlength l = n_pre |- _ => rewrite <- Hlen
  end.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed. 

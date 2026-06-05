Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260605_012416v_array_sum_positive Require Import array_sum_positive_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_sum_positive.
Local Open Scope sac.

Lemma array_sum_positive_spec_nonneg :
  forall l, 0 <= array_sum_positive_spec l.
Proof.
  intros l.
  induction l as [| x xs IH].
  - simpl. lia.
  - simpl. destruct (Z_gt_dec x 0); lia.
Qed.

Lemma array_sum_positive_spec_app :
  forall l1 l2,
    array_sum_positive_spec (l1 ++ l2) =
    array_sum_positive_spec l1 + array_sum_positive_spec l2.
Proof.
  intros l1 l2.
  induction l1 as [| x xs IH].
  - simpl. lia.
  - simpl. destruct (Z_gt_dec x 0); rewrite IH; lia.
Qed.

Lemma array_sum_positive_spec_sublist_succ :
  forall l i,
    0 <= i < Zlength l ->
    array_sum_positive_spec (sublist 0 (i + 1) l) =
    array_sum_positive_spec (sublist 0 i l) +
    (if Z_gt_dec (Znth i l 0) 0 then Znth i l 0 else 0).
Proof.
  intros l i Hi.
  rewrite (sublist_split 0 (i + 1) i l); try lia.
  rewrite array_sum_positive_spec_app.
  rewrite (sublist_single 0 i l); try lia.
  simpl. destruct (Z_gt_dec (Znth i l 0) 0); lia.
Qed.

Lemma array_sum_positive_spec_prefix_le :
  forall l hi,
    0 <= hi <= Zlength l ->
    array_sum_positive_spec (sublist 0 hi l) <= array_sum_positive_spec l.
Proof.
  intros l hi Hhi.
  assert (Hsplit :
    l = sublist 0 hi l ++ sublist hi (Zlength l) l).
  {
    rewrite <- (sublist_self l (Zlength l)) at 1 by reflexivity.
    rewrite (sublist_split 0 (Zlength l) hi l) by lia.
    reflexivity.
  }
  rewrite Hsplit at 2.
  rewrite array_sum_positive_spec_app.
  pose proof array_sum_positive_spec_nonneg (sublist hi (Zlength l) l) as Hnonneg.
  lia.
Qed.

Lemma proof_of_array_sum_positive_safety_wit_4 : array_sum_positive_safety_wit_4.
Proof.
  pre_process.
  entailer!.
  assert (Hstep :
    sum + Znth i l 0 = array_sum_positive_spec (sublist 0 (i + 1) l)).
  {
    rewrite H4.
    rewrite array_sum_positive_spec_sublist_succ; try lia.
    destruct (Z_gt_dec (Znth i l 0) 0); lia.
  }
  assert (Hle :
    array_sum_positive_spec (sublist 0 (i + 1) l) <= array_sum_positive_spec l).
  {
    apply array_sum_positive_spec_prefix_le.
    rewrite H6. lia.
  }
  lia.
Qed.

Lemma proof_of_array_sum_positive_entail_wit_1 : array_sum_positive_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_array_sum_positive_entail_wit_2_1 : array_sum_positive_entail_wit_2_1.
Proof.
  pre_process.
  entailer!.
  rewrite H4.
  rewrite array_sum_positive_spec_sublist_succ; try lia.
  destruct (Z_gt_dec (Znth i l 0) 0); lia.
Qed.

Lemma proof_of_array_sum_positive_entail_wit_2_2 : array_sum_positive_entail_wit_2_2.
Proof.
  pre_process.
  entailer!.
  rewrite H4.
  rewrite array_sum_positive_spec_sublist_succ; try lia.
  destruct (Z_gt_dec (Znth i l 0) 0); lia.
Qed.

Lemma proof_of_array_sum_positive_return_wit_1 : array_sum_positive_return_wit_1.
Proof.
  pre_process.
  assert (i = n_pre) by lia.
  subst i.
  rewrite <- H5 in H3.
  rewrite sublist_self in H3 by reflexivity.
  entailer!.
Qed.

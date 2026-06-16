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
From SimpleC.EE.CAV.verify_20260608_185604_p073_smallest_change Require Import p073_smallest_change_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p073_smallest_change.
Local Open Scope sac.

Lemma proof_of_p073_smallest_change_safety_wit_9 : p073_smallest_change_safety_wit_9.
Proof.
  unfold p073_smallest_change_safety_wit_9, derivable1, andp, coq_prop.
  intros.
  destruct H as [H Hsep].
  repeat match type of H with _ /\ _ => destruct H end.
  assert (Hhalf_pre : 2 * i < arr_size_pre) by lia.
  assert (Hhalf : 2 * i < Zlength lv).
  { rewrite <- H2. exact Hhalf_pre. }
  destruct (H0 i H7 Hhalf) as [_ Hplus].
  rewrite H5.
  destruct Hplus as [Hmin Hmax].
  split; lia.
Qed.

Lemma proof_of_p073_smallest_change_entail_wit_1 : p073_smallest_change_entail_wit_1.
Proof.
  unfold p073_smallest_change_entail_wit_1, derivable1, andp, coq_prop.
  intros.
  repeat match type of H with _ /\ _ => destruct H end.
  repeat split; try lia; try assumption.
  all: match goal with
       | Hrange : smallest_change_int_range _,
         Hlo : 0 <= ?k,
         Hhi : 2 * ?k < Zlength _
          |- _ =>
           destruct (Hrange _ Hlo Hhi); lia
       end.
Qed.

Lemma proof_of_p073_smallest_change_entail_wit_2_1 : p073_smallest_change_entail_wit_2_1.
Proof.
  unfold p073_smallest_change_entail_wit_2_1, derivable1, andp, coq_prop.
  intros.
  repeat match type of H with _ /\ _ => destruct H end.
  repeat split; try assumption; try lia.
  rewrite H6.
  unfold count_half_mismatches_upto.
  assert (Hnat: Z.to_nat (i + 1) = S (Z.to_nat i)).
  { rewrite Z2Nat.inj_add by lia. simpl. lia. }
  rewrite Hnat. simpl.
  rewrite Z2Nat.id by lia.
  rewrite H3 in H.
  apply Z.eqb_neq in H.
  rewrite H.
  lia.
  all: match goal with
       | Hrange : smallest_change_int_range _,
         Hlo : 0 <= ?k,
         Hhi : 2 * ?k < Zlength _
         |- _ =>
           destruct (Hrange _ Hlo Hhi); lia
       end.
Qed.

Lemma proof_of_p073_smallest_change_entail_wit_2_2 : p073_smallest_change_entail_wit_2_2.
Proof.
  unfold p073_smallest_change_entail_wit_2_2, derivable1, andp, coq_prop.
  intros.
  repeat match type of H with _ /\ _ => destruct H end.
  repeat split; try assumption; try lia.
  rewrite H6.
  unfold count_half_mismatches_upto.
  assert (Hnat: Z.to_nat (i + 1) = S (Z.to_nat i)).
  { rewrite Z2Nat.inj_add by lia. simpl. lia. }
  rewrite Hnat. simpl.
  rewrite Z2Nat.id by lia.
  rewrite H3 in H.
  apply Z.eqb_eq in H.
  rewrite H.
  lia.
  all: match goal with
       | Hrange : smallest_change_int_range _,
         Hlo : 0 <= ?k,
         Hhi : 2 * ?k < Zlength _
         |- _ =>
           destruct (Hrange _ Hlo Hhi); lia
       end.
Qed.

Lemma proof_of_p073_smallest_change_return_wit_1 : p073_smallest_change_return_wit_1.
Proof.
  unfold p073_smallest_change_return_wit_1, derivable1, andp, coq_prop.
  intros.
  repeat match type of H with _ /\ _ => destruct H end.
  split; [| exact H0].
  unfold problem_73_spec.
  rewrite H6.
  rewrite <- H3.
  assert (Hi: i = arr_size_pre / 2).
  {
    apply Z.div_unique with (r := arr_size_pre - 2 * i).
    all: lia.
  }
  now rewrite Hi.
Qed.

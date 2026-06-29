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
From SimpleC.EE.CAV.ground_truth_p066_digitSum Require Import p066_digitSum_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
From AUXLib Require Import ListLib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import string_bridge.

Import naive_C_Rules.
Require Import p066_digitSum.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p066_digitSum.v so public contract files expose definitions only. *)

Lemma sum_upper_upto_0 : forall l,
  sum_upper_upto 0 l = 0.
Proof.
  intros l.
  unfold sum_upper_upto.
  reflexivity.
Qed.
Lemma sum_upper_list_app : forall l1 l2,
  sum_upper_list (l1 ++ l2) =
  sum_upper_list l1 + sum_upper_list l2.
Proof.
  induction l1 as [| x xs IH]; intros l2; simpl.
  - lia.
  - rewrite IH. lia.
Qed.
Lemma firstn_succ_snoc : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = List.app (firstn n l) [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.
Lemma firstn_succ_Znth : forall (l : list Z) i,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  List.app (firstn (Z.to_nat i) l) [Znth i l 0].
Proof.
  intros l i H.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc with (d := 0).
  - reflexivity.
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
Qed.
Lemma sum_upper_upto_step_upper : forall i l,
  0 <= i ->
  i < Zlength l ->
  65 <= Znth i l 0 ->
  Znth i l 0 <= 90 ->
  sum_upper_upto (i + 1) l =
  sum_upper_upto i l + Znth i l 0.
Proof.
  intros i l Hi Hlt Hlo Hhi.
  unfold sum_upper_upto.
  rewrite firstn_succ_Znth by lia.
  rewrite sum_upper_list_app.
  simpl.
  unfold is_upper.
  replace (Z.leb 65 (Znth i l 0)) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb (Znth i l 0) 90) with true by (symmetry; apply Z.leb_le; lia).
  simpl. lia.
Qed.
Lemma sum_upper_upto_step_not_upper : forall i l,
  0 <= i ->
  i < Zlength l ->
  (Znth i l 0 < 65 \/ 90 < Znth i l 0) ->
  sum_upper_upto (i + 1) l =
  sum_upper_upto i l.
Proof.
  intros i l Hi Hlt Hnot.
  unfold sum_upper_upto.
  rewrite firstn_succ_Znth by lia.
  rewrite sum_upper_list_app.
  simpl.
  unfold is_upper.
  destruct Hnot as [Hlo | Hhi].
  - replace (Z.leb 65 (Znth i l 0)) with false by (symmetry; apply Z.leb_gt; lia).
    simpl. lia.
  - replace (Z.leb 65 (Znth i l 0)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.leb (Znth i l 0) 90) with false by (symmetry; apply Z.leb_gt; lia).
    simpl. lia.
Qed.
Lemma problem_66_spec_intro : forall s output,
  output = sum_upper_upto (Zlength s) s ->
  problem_66_spec s output.
Proof.
  intros s output Hout.
  unfold problem_66_spec.
  rewrite Hout.
  unfold sum_upper_upto.
  replace (Z.to_nat (Zlength s)) with (List.length s)
    by (rewrite Zlength_correct; lia).
  rewrite firstn_all.
  reflexivity.
Qed.


Lemma proof_of_p066_digitSum_safety_wit_5 : p066_digitSum_safety_wit_5.
Proof.
  unfold p066_digitSum_safety_wit_5.
  intros.
  pre_process.
  subst sum.
  match goal with
  | Hrange : digit_sum_int_range l |- _ =>
      destruct (Hrange i ltac:(lia) ltac:(lia)) as [_ Hadd]
  end.
  rewrite app_Znth1 by lia.
  entailer!.
Qed.

Lemma proof_of_p066_digitSum_entail_wit_1 : p066_digitSum_entail_wit_1.
Proof.
  unfold p066_digitSum_entail_wit_1.
  intros.
  pre_process.
  subst retval.
  rewrite sum_upper_upto_0.
  entailer!.
Qed.

Lemma proof_of_p066_digitSum_entail_wit_2_1 : p066_digitSum_entail_wit_2_1.
Proof.
  unfold p066_digitSum_entail_wit_2_1.
  intros.
  pre_process.
  subst sum.
  rewrite app_Znth1 in * by lia.
  rewrite sum_upper_upto_step_upper by lia.
  entailer!.
Qed.

Lemma proof_of_p066_digitSum_entail_wit_2_2 : p066_digitSum_entail_wit_2_2.
Proof.
  unfold p066_digitSum_entail_wit_2_2.
  intros.
  pre_process.
  subst sum.
  rewrite app_Znth1 in * by lia.
  rewrite sum_upper_upto_step_not_upper by lia.
  entailer!.
Qed.

Lemma proof_of_p066_digitSum_entail_wit_2_3 : p066_digitSum_entail_wit_2_3.
Proof.
  unfold p066_digitSum_entail_wit_2_3.
  intros.
  pre_process.
  subst sum.
  rewrite app_Znth1 in * by lia.
  rewrite sum_upper_upto_step_not_upper by lia.
  entailer!.
Qed.

Lemma proof_of_p066_digitSum_return_wit_1 : p066_digitSum_return_wit_1.
Proof.
  unfold p066_digitSum_return_wit_1.
  intros.
  pre_process.
  subst sum.
  assert (i = len) by lia.
  subst i.
  entailer!.
  eapply problem_66_spec_intro; eauto.
  rewrite H2.
  reflexivity.
Qed.

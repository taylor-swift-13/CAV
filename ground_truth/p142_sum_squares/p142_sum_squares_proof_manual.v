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
From SimpleC.EE.CAV.ground_truth_p142_sum_squares Require Import p142_sum_squares_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Lists.List Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p142_sum_squares.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p142_sum_squares.v so public contract files expose definitions only. *)

Lemma transformed_sum_from_app_single : forall xs x start,
  transformed_sum_from (xs ++ x :: nil) start =
  transformed_sum_from xs start + transformed_value (start + Zlength xs) x.
Proof.
  induction xs; intros x start; simpl.
  - change (Zlength (@nil Z)) with 0.
    rewrite Z.add_0_r.
    rewrite Z.add_0_r.
    reflexivity.
  - rewrite IHxs.
    rewrite Zlength_cons.
    replace (Z.succ (Zlength xs)) with (1 + Zlength xs) by lia.
    replace (start + 1 + Zlength xs) with (start + (1 + Zlength xs)) by lia.
    rewrite Z.add_assoc.
    reflexivity.
Qed.
Lemma transformed_prefix_sum_0 : forall l,
  transformed_prefix_sum 0 l = 0.
Proof.
  intros l.
  unfold transformed_prefix_sum, sublist.
  simpl.
  reflexivity.
Qed.
Lemma transformed_prefix_sum_snoc : forall l i,
  0 <= i < Zlength l ->
  transformed_prefix_sum (i + 1) l =
  transformed_prefix_sum i l + transformed_value i (Znth i l 0).
Proof.
  intros l i Hi.
  unfold transformed_prefix_sum.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single 0 i l) by lia.
  rewrite transformed_sum_from_app_single.
  rewrite Zlength_sublist by lia.
  replace (0 + (i - 0)) with i by lia.
  reflexivity.
Qed.
Lemma transformed_prefix_sum_full : forall l,
  transformed_prefix_sum (Zlength l) l = transformed_sum_from l 0.
Proof.
  intros l.
  unfold transformed_prefix_sum.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed.
Lemma problem_142_spec_of_prefix_full : forall l out,
  out = transformed_prefix_sum (Zlength l) l ->
  problem_142_spec l out.
Proof.
  intros l out Hout.
  unfold problem_142_spec.
  rewrite Hout.
  apply transformed_prefix_sum_full.
Qed.
Lemma sum_squares_next_range : forall l i,
  sum_squares_int_range l ->
  0 <= i < Zlength l ->
  INT_MIN <= transformed_prefix_sum i l + transformed_value i (Znth i l 0) <= INT_MAX.
Proof.
  intros l i [Hstep _] Hi.
  pose proof (Hstep i Hi) as [_ [_ Hsum]].
  exact Hsum.
Qed.
Lemma sum_squares_square_range : forall l i,
  sum_squares_int_range l ->
  0 <= i < Zlength l ->
  INT_MIN <= Znth i l 0 * Znth i l 0 <= INT_MAX.
Proof.
  intros l i [Hstep _] Hi.
  pose proof (Hstep i Hi) as [Hsq _].
  exact Hsq.
Qed.
Lemma sum_squares_cube_range : forall l i,
  sum_squares_int_range l ->
  0 <= i < Zlength l ->
  INT_MIN <= Znth i l 0 * Znth i l 0 * Znth i l 0 <= INT_MAX.
Proof.
  intros l i [Hstep _] Hi.
  pose proof (Hstep i Hi) as [_ [Hcube _]].
  exact Hcube.
Qed.
Lemma transformed_value_square : forall i x,
  Z.rem i 3 = 0 ->
  transformed_value i x = x * x.
Proof.
  intros i x H.
  unfold transformed_value.
  apply Z.eqb_eq in H.
  rewrite H.
  reflexivity.
Qed.
Lemma transformed_value_cube : forall i x,
  Z.rem i 3 <> 0 ->
  Z.rem i 4 = 0 ->
  transformed_value i x = x * x * x.
Proof.
  intros i x H3 H4.
  unfold transformed_value.
  apply Z.eqb_neq in H3.
  apply Z.eqb_eq in H4.
  rewrite H3, H4.
  reflexivity.
Qed.
Lemma transformed_value_plain : forall i x,
  Z.rem i 3 <> 0 ->
  Z.rem i 4 <> 0 ->
  transformed_value i x = x.
Proof.
  intros i x H3 H4.
  unfold transformed_value.
  apply Z.eqb_neq in H3.
  apply Z.eqb_neq in H4.
  rewrite H3, H4.
  reflexivity.
Qed.


Lemma proof_of_p142_sum_squares_safety_wit_6 : p142_sum_squares_safety_wit_6.
Proof.
  pre_process.
  subst sum.
  pose proof (sum_squares_next_range input_l i H5 ltac:(lia)) as Hrange.
  rewrite transformed_value_square in Hrange by assumption.
  entailer!.
Qed.

Lemma proof_of_p142_sum_squares_safety_wit_7 : p142_sum_squares_safety_wit_7.
Proof.
  pre_process.
  pose proof (sum_squares_square_range input_l i H5 ltac:(lia)) as Hrange.
  entailer!.
Qed.

Lemma proof_of_p142_sum_squares_safety_wit_11 : p142_sum_squares_safety_wit_11.
Proof.
  pre_process.
  subst sum.
  pose proof (sum_squares_next_range input_l i H6 ltac:(lia)) as Hrange.
  rewrite transformed_value_cube in Hrange by assumption.
  entailer!.
Qed.

Lemma proof_of_p142_sum_squares_safety_wit_12 : p142_sum_squares_safety_wit_12.
Proof.
  pre_process.
  pose proof (sum_squares_cube_range input_l i H6 ltac:(lia)) as Hrange.
  entailer!.
Qed.

Lemma proof_of_p142_sum_squares_safety_wit_13 : p142_sum_squares_safety_wit_13.
Proof.
  pre_process.
  pose proof (sum_squares_square_range input_l i H6 ltac:(lia)) as Hrange.
  entailer!.
Qed.

Lemma proof_of_p142_sum_squares_safety_wit_17 : p142_sum_squares_safety_wit_17.
Proof.
  pre_process.
  subst sum.
  pose proof (sum_squares_next_range input_l i H6 ltac:(lia)) as Hrange.
  rewrite transformed_value_plain in Hrange by assumption.
  entailer!.
Qed.

Lemma proof_of_p142_sum_squares_entail_wit_1 : p142_sum_squares_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_p142_sum_squares_entail_wit_2_1 : p142_sum_squares_entail_wit_2_1.
Proof.
  pre_process.
  subst sum.
  entailer!.
  rewrite transformed_prefix_sum_snoc by lia.
  rewrite transformed_value_square by assumption.
  reflexivity.
Qed.

Lemma proof_of_p142_sum_squares_entail_wit_2_2 : p142_sum_squares_entail_wit_2_2.
Proof.
  pre_process.
  subst sum.
  entailer!.
  rewrite transformed_prefix_sum_snoc by lia.
  rewrite transformed_value_cube by assumption.
  reflexivity.
Qed.

Lemma proof_of_p142_sum_squares_entail_wit_2_3 : p142_sum_squares_entail_wit_2_3.
Proof.
  pre_process.
  subst sum.
  entailer!.
  rewrite transformed_prefix_sum_snoc by lia.
  rewrite transformed_value_plain by assumption.
  reflexivity.
Qed.

Lemma proof_of_p142_sum_squares_return_wit_1 : p142_sum_squares_return_wit_1.
Proof.
  pre_process.
  replace i with lst_size_pre in * by lia.
  subst sum.
  entailer!.
  apply problem_142_spec_of_prefix_full.
  rewrite <- H2.
  reflexivity.
Qed.

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
From SimpleC.EE.CAV.ground_truth_p085_add Require Import p085_add_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Bool.Bool.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p085_add.
Local Open Scope sac.
Require Import Lia.

Local Open Scope list_scope.

(* Proof helpers moved from p085_add.v so public contract files expose definitions only. *)

Lemma sum_even_at_odd_upto_0 : forall l,
  sum_even_at_odd_upto 0 l = 0.
Proof.
  intros l.
  unfold sum_even_at_odd_upto.
  reflexivity.
Qed.
Lemma sum_even_at_odd_upto_step_even : forall i l,
  0 <= i ->
  Z.rem (Znth (2 * i + 1) l 0) 2 = 0 ->
  sum_even_at_odd_upto (i + 1) l =
  sum_even_at_odd_upto i l + Znth (2 * i + 1) l 0.
Proof.
  intros i l Hi Heven.
  unfold sum_even_at_odd_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  change ((match i with
           | 0 => 0
           | Z.pos y' => Z.pos y'~0
           | Z.neg y' => Z.neg y'~0
           end) + 1) with (2 * i + 1).
  destruct (Z.eqb (Z.rem (Znth (2 * i + 1) l 0) 2) 0) eqn:Heq.
  - reflexivity.
  - apply Z.eqb_neq in Heq. congruence.
Qed.
Lemma sum_even_at_odd_upto_step_odd : forall i l,
  0 <= i ->
  Z.rem (Znth (2 * i + 1) l 0) 2 <> 0 ->
  sum_even_at_odd_upto (i + 1) l =
  sum_even_at_odd_upto i l.
Proof.
  intros i l Hi Hodd.
  unfold sum_even_at_odd_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  change ((match i with
           | 0 => 0
           | Z.pos y' => Z.pos y'~0
           | Z.neg y' => Z.neg y'~0
           end) + 1) with (2 * i + 1).
  destruct (Z.eqb (Z.rem (Znth (2 * i + 1) l 0) 2) 0) eqn:Heq.
  - apply Z.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.
Lemma problem_85_exit_index : forall (l : list Z) i,
  0 <= i ->
  2 * i <= Zlength l ->
  2 * i + 1 >= Zlength l ->
  i = Zlength l / 2.
Proof.
  intros l i Hi Hlow Hexit.
  apply Z.div_unique with (r := Zlength l - 2 * i).
  - left. lia.
  - lia.
Qed.
Lemma problem_85_spec_of_exit : forall (l : list Z) i s,
  0 <= i ->
  2 * i <= Zlength l ->
  2 * i + 1 >= Zlength l ->
  s = sum_even_at_odd_upto i l ->
  problem_85_spec l s.
Proof.
  intros l i s Hi Hbound Hexit Hs.
  unfold problem_85_spec.
  subst s.
  rewrite <- (problem_85_exit_index l i); auto.
Qed.


Lemma proof_of_p085_add_safety_wit_14 : p085_add_safety_wit_14.
Proof.
  pre_process.
  subst s.
  match goal with
  | H: add_int_range lv |- _ =>
      destruct (H i ltac:(lia) ltac:(lia)) as [_ Hsum]
  end.
  entailer!;
  replace (i * 2 + 1) with (2 * i + 1) by lia;
  lia.
Qed.

Lemma proof_of_p085_add_entail_wit_1 : p085_add_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_p085_add_entail_wit_2_1 : p085_add_entail_wit_2_1.
Proof.
  pre_process.
  replace (i * 2 + 1) with (2 * i + 1) in * by lia.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  rewrite sum_even_at_odd_upto_step_even by lia.
  lia.
Qed.

Lemma proof_of_p085_add_entail_wit_2_2 : p085_add_entail_wit_2_2.
Proof.
  pre_process.
  replace (i * 2 + 1) with (2 * i + 1) in * by lia.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  rewrite sum_even_at_odd_upto_step_odd by lia.
  assumption.
Qed.

Lemma proof_of_p085_add_return_wit_1 : p085_add_return_wit_1.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply problem_85_spec_of_exit with (i := i); auto; lia.
Qed.

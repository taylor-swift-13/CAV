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
From SimpleC.EE.CAV.ground_truth_p073_smallest_change Require Import p073_smallest_change_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
From AUXLib Require Import ListLib.
Require Import Coq.micromega.Lia.

Import naive_C_Rules.
Require Import p073_smallest_change.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p073_smallest_change.v so public contract files expose definitions only. *)

Lemma count_half_mismatches_upto_0 : forall arr,
  count_half_mismatches_upto 0 arr = 0.
Proof.
  reflexivity.
Qed.
Lemma count_half_mismatches_upto_step_eq : forall arr i,
  0 <= i ->
  Znth i arr 0 = Znth (Zlength arr - 1 - i) arr 0 ->
  count_half_mismatches_upto (i + 1) arr =
    count_half_mismatches_upto i arr.
Proof.
  intros arr i Hi Heq.
  unfold count_half_mismatches_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  rewrite Heq.
  rewrite Z.eqb_refl.
  lia.
Qed.
Lemma count_half_mismatches_upto_step_neq : forall arr i,
  0 <= i ->
  Znth i arr 0 <> Znth (Zlength arr - 1 - i) arr 0 ->
  count_half_mismatches_upto (i + 1) arr =
    count_half_mismatches_upto i arr + 1.
Proof.
  intros arr i Hi Hneq.
  unfold count_half_mismatches_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  destruct (Z.eqb (Znth i arr 0) (Znth (Zlength arr - 1 - i) arr 0)) eqn:Heq.
  - apply Z.eqb_eq in Heq. contradiction.
  - lia.
Qed.
Lemma problem_73_exit_index : forall (arr : list Z) i,
  0 <= i ->
  2 * i <= Zlength arr ->
  i >= Zlength arr - 1 - i ->
  Z.to_nat i = (length arr / 2)%nat.
Proof.
  intros arr i Hi Hlow Hhigh.
  apply Nat2Z.inj.
  rewrite Z2Nat.id by lia.
  rewrite Nat2Z.inj_div.
  change (Z.of_nat 2) with 2.
  rewrite <- Zlength_correct.
  apply Z.div_unique with (r := Zlength arr - 2 * i).
  - left. lia.
  - lia.
Qed.
Lemma problem_73_spec_of_exit : forall arr i out,
  0 <= i ->
  2 * i <= Zlength arr ->
  i >= Zlength arr - 1 - i ->
  out = count_half_mismatches_upto i arr ->
  problem_73_spec arr out.
Proof.
  intros arr i out Hi Hbound Hexit Hout.
  unfold problem_73_spec.
  subst out.
  unfold count_half_mismatches_upto.
  pose proof (problem_73_exit_index arr i Hi Hbound Hexit) as Hidx.
  rewrite Hidx.
  rewrite Zlength_correct.
  rewrite Z2Nat.inj_div by lia.
  rewrite Nat2Z.id.
  reflexivity.
Qed.


Lemma proof_of_p073_smallest_change_safety_wit_9 : p073_smallest_change_safety_wit_9.
Proof.
  pre_process.
  subst out.
  match goal with
  | H: smallest_change_int_range lv |- _ =>
      destruct (H i ltac:(lia) ltac:(lia)) as [_ Hnext]
  end.
  entailer!.
Qed.

Lemma proof_of_p073_smallest_change_entail_wit_1 : p073_smallest_change_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_p073_smallest_change_entail_wit_2_1 : p073_smallest_change_entail_wit_2_1.
Proof.
  pre_process.
  subst out.
  rewrite count_half_mismatches_upto_step_neq.
  entailer!.
  - lia.
  - rewrite <- H3. exact H.
Qed.

Lemma proof_of_p073_smallest_change_entail_wit_2_2 : p073_smallest_change_entail_wit_2_2.
Proof.
  pre_process.
  subst out.
  rewrite count_half_mismatches_upto_step_eq.
  entailer!.
  - lia.
  - rewrite <- H3. exact H.
Qed.

Lemma proof_of_p073_smallest_change_return_wit_1 : p073_smallest_change_return_wit_1.
Proof.
  pre_process.
  entailer!.
  apply problem_73_spec_of_exit with (i := i); auto; lia.
Qed.

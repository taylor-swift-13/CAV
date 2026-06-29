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
From SimpleC.EE.CAV.ground_truth_p121_solutions Require Import p121_solutions_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool.

Import naive_C_Rules.
Require Import p121_solutions.
Local Open Scope sac.
Require Import Lia.

Local Open Scope list_scope.

(* Proof helpers moved from p121_solutions.v so public contract files expose definitions only. *)

Lemma sum_odd_at_even_upto_0 : forall l,
  sum_odd_at_even_upto 0 l = 0.
Proof.
  intros l.
  unfold sum_odd_at_even_upto.
  reflexivity.
Qed.
Lemma sum_odd_at_even_upto_step_odd : forall i l,
  0 <= i ->
  Z.rem (Znth (2 * i) l 0) 2 = 1 ->
  sum_odd_at_even_upto (i + 1) l =
  sum_odd_at_even_upto i l + Znth (2 * i) l 0.
Proof.
  intros i l Hi Hodd.
  unfold sum_odd_at_even_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  change (match i with
          | 0 => 0
          | Z.pos y' => Z.pos y'~0
          | Z.neg y' => Z.neg y'~0
          end) with (2 * i).
  destruct (Z.eqb (Z.rem (Znth (2 * i) l 0) 2) 1) eqn:Heq.
  - reflexivity.
  - apply Z.eqb_neq in Heq. congruence.
Qed.
Lemma sum_odd_at_even_upto_step_not_odd : forall i l,
  0 <= i ->
  Z.rem (Znth (2 * i) l 0) 2 <> 1 ->
  sum_odd_at_even_upto (i + 1) l =
  sum_odd_at_even_upto i l.
Proof.
  intros i l Hi Hnot.
  unfold sum_odd_at_even_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  change (match i with
          | 0 => 0
          | Z.pos y' => Z.pos y'~0
          | Z.neg y' => Z.neg y'~0
          end) with (2 * i).
  destruct (Z.eqb (Z.rem (Znth (2 * i) l 0) 2) 1) eqn:Heq.
  - apply Z.eqb_eq in Heq. congruence.
  - reflexivity.
Qed.
Lemma Znth_default_ge_121 : forall (l : list Z) i d,
  Zlength l <= i ->
  Znth i l d = d.
Proof.
  intros l i d Hi.
  unfold Znth.
  apply nth_overflow.
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma sum_odd_at_even_upto_step_out : forall i l,
  0 <= i ->
  Zlength l <= 2 * i ->
  sum_odd_at_even_upto (i + 1) l = sum_odd_at_even_upto i l.
Proof.
  intros i l Hi Hout.
  unfold sum_odd_at_even_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  change (match i with
          | 0 => 0
          | Z.pos y' => Z.pos y'~0
          | Z.neg y' => Z.neg y'~0
          end) with (2 * i).
  rewrite Znth_default_ge_121 by lia.
  reflexivity.
Qed.
Lemma sum_odd_at_even_upto_stable : forall i j l,
  0 <= i ->
  i <= j ->
  Zlength l <= 2 * i ->
  sum_odd_at_even_upto j l = sum_odd_at_even_upto i l.
Proof.
  intros i j l Hi Hij Hout.
  assert (Hstable : forall n,
    sum_odd_at_even_upto (i + Z.of_nat n) l = sum_odd_at_even_upto i l).
  {
    induction n.
    - replace (i + Z.of_nat 0) with i by lia.
      reflexivity.
    - replace (i + Z.of_nat (S n)) with ((i + Z.of_nat n) + 1) by lia.
      transitivity (sum_odd_at_even_upto (i + Z.of_nat n) l).
      + apply sum_odd_at_even_upto_step_out.
        * pose proof (Nat2Z.is_nonneg n). lia.
        * pose proof (Nat2Z.is_nonneg n). lia.
      + apply IHn.
  }
  replace j with (i + Z.of_nat (Z.to_nat (j - i))).
  - apply Hstable.
  - rewrite Z2Nat.id by lia.
    lia.
Qed.
Lemma problem_121_spec_of_exit : forall l i s,
  0 <= i ->
  2 * i <= Zlength l + 1 ->
  Zlength l <= 2 * i ->
  s = sum_odd_at_even_upto i l ->
  problem_121_spec l s.
Proof.
  intros l i s Hi Hbound Hexit Hs.
  unfold problem_121_spec.
  subst s.
  symmetry.
  apply sum_odd_at_even_upto_stable.
  - lia.
  - pose proof (Zlength_nonneg l). lia.
  - lia.
Qed.


Lemma proof_of_p121_solutions_safety_wit_10 : p121_solutions_safety_wit_10.
Proof.
  pre_process.
  subst s.
  match goal with
  | H: sum_odd_at_even_int_range lv |- _ =>
      destruct (H i ltac:(lia) ltac:(lia)) as [_ Hsum]
  end.
  entailer!;
  replace (i * 2) with (2 * i) by lia;
  lia.
Qed. 

Lemma proof_of_p121_solutions_entail_wit_1 : p121_solutions_entail_wit_1.
Proof.
  pre_process.
Qed. 

Lemma proof_of_p121_solutions_entail_wit_2_1 : p121_solutions_entail_wit_2_1.
Proof.
  pre_process.
  replace (i * 2) with (2 * i) in * by lia.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  rewrite sum_odd_at_even_upto_step_odd by lia.
  lia.
Qed. 

Lemma proof_of_p121_solutions_entail_wit_2_2 : p121_solutions_entail_wit_2_2.
Proof.
  pre_process.
  replace (i * 2) with (2 * i) in * by lia.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  rewrite sum_odd_at_even_upto_step_not_odd by lia.
  assumption.
Qed. 

Lemma proof_of_p121_solutions_return_wit_1 : p121_solutions_return_wit_1.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply problem_121_spec_of_exit with (i := i); auto; lia.
Qed. 

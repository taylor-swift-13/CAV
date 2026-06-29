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
From SimpleC.EE.CAV.ground_truth_p126_is_sorted Require Import p126_is_sorted_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Arith.Arith.

Import naive_C_Rules.
Require Import p126_is_sorted.
Local Open Scope sac.
Require Import Lia.
From AUXLib Require Import ListLib.

Local Open Scope list_scope.

(* Proof helpers moved from p126_is_sorted.v so public contract files expose definitions only. *)

Lemma sorted_no_triple_prefix_1 : forall l,
  sorted_no_triple_prefix 1 l.
Proof.
  intros l.
  unfold sorted_no_triple_prefix.
  split; intros j Hj; lia.
Qed.
Lemma sorted_no_triple_prefix_step : forall l i,
  1 <= i ->
  sorted_no_triple_prefix i l ->
  Znth (i - 1) l 0 <= Znth i l 0 ->
  ~ (2 <= i /\ Znth i l 0 = Znth (i - 1) l 0 /\ Znth i l 0 = Znth (i - 2) l 0) ->
  sorted_no_triple_prefix (i + 1) l.
Proof.
  intros l i Hi [Hsorted Htriple] Hle Hnot.
  unfold sorted_no_triple_prefix.
  split.
  - intros j Hj.
    destruct (Z.eq_dec j i) as [-> | Hne].
    + exact Hle.
    + apply Hsorted. lia.
  - intros j Hj.
    destruct (Z.eq_dec j i) as [-> | Hne].
    + intro Hbad. apply Hnot. tauto.
    + apply Htriple. lia.
Qed.
Lemma problem_126_spec_true_of_exit : forall l i,
  problem_126_pre l ->
  i >= Zlength l ->
  i <= Zlength l ->
  sorted_no_triple_prefix i l ->
  problem_126_spec l true.
Proof.
  intros l i _ Hge Hle Hprefix.
  replace i with (Zlength l) in Hprefix by lia.
  unfold problem_126_spec.
  split; intros _.
  - reflexivity.
  - exact Hprefix.
Qed.
Lemma problem_126_spec_false_of_desc : forall l i,
  problem_126_pre l ->
  1 <= i ->
  i < Zlength l ->
  Znth i l 0 < Znth (i - 1) l 0 ->
  problem_126_spec l false.
Proof.
  intros l i _ Hi Hlen Hlt.
  unfold problem_126_spec.
  split.
  - intros [Hsorted _].
    pose proof (Hsorted i ltac:(lia)).
    lia.
  - discriminate.
Qed.
Lemma problem_126_spec_false_of_triple : forall l i,
  problem_126_pre l ->
  2 <= i ->
  i < Zlength l ->
  Znth i l 0 = Znth (i - 1) l 0 ->
  Znth i l 0 = Znth (i - 2) l 0 ->
  problem_126_spec l false.
Proof.
  intros l i _ Hi Hlen Heq1 Heq2.
  unfold problem_126_spec.
  split.
  - intros [_ Htriple].
    exfalso.
    apply (Htriple i ltac:(lia)).
    split; assumption.
  - discriminate.
Qed.


Lemma proof_of_p126_is_sorted_entail_wit_1 : p126_is_sorted_entail_wit_1.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply sorted_no_triple_prefix_1.
Qed. 

Lemma proof_of_p126_is_sorted_entail_wit_2_1 : p126_is_sorted_entail_wit_2_1.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  eapply sorted_no_triple_prefix_step.
  - lia.
  - eassumption.
  - lia.
  - intros [_ [Heq _]]. contradiction.
Qed. 

Lemma proof_of_p126_is_sorted_entail_wit_2_2 : p126_is_sorted_entail_wit_2_2.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  eapply sorted_no_triple_prefix_step.
  - lia.
  - eassumption.
  - lia.
  - intros [Hge _]. lia.
Qed. 

Lemma proof_of_p126_is_sorted_entail_wit_2_3 : p126_is_sorted_entail_wit_2_3.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  eapply sorted_no_triple_prefix_step.
  - lia.
  - eassumption.
  - lia.
  - intros [_ [_ Heq]]. contradiction.
Qed. 

Lemma proof_of_p126_is_sorted_return_wit_1 : p126_is_sorted_return_wit_1.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  right.
  split.
  - hnf. lia.
  - split.
    + hnf. apply problem_126_spec_true_of_exit with (i := i); auto; lia.
    + assumption.
Qed. 

Lemma proof_of_p126_is_sorted_return_wit_2 : p126_is_sorted_return_wit_2.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  left.
  split.
  - hnf. reflexivity.
  - split.
    + hnf. apply problem_126_spec_false_of_triple with (i := i); auto; lia.
    + assumption.
Qed. 

Lemma proof_of_p126_is_sorted_return_wit_3 : p126_is_sorted_return_wit_3.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  left.
  split.
  - hnf. reflexivity.
  - split.
    + hnf. apply problem_126_spec_false_of_desc with (i := i); auto; lia.
    + assumption.
Qed. 

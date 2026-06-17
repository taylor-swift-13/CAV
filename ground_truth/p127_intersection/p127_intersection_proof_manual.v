Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p127_intersection Require Import p127_intersection_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p127_intersection.
Local Open Scope sac.

Ltac prepare_127 :=
  pre_process;
  subst;
  match goal with
  | H1 : interval_int_range ?l1, H2 : interval_int_range ?l2 |- _ =>
      let Hkeep1 := fresh "Hrange_keep" in
      let Hkeep2 := fresh "Hrange_keep" in
      let Hlen1 := fresh "Hlen" in
      let Hrange1 := fresh "Hrange" in
      let Hlen2 := fresh "Hlen" in
      let Hrange2 := fresh "Hrange" in
      pose proof H1 as Hkeep1;
      pose proof H2 as Hkeep2;
      unfold interval_int_range in H1, H2;
      destruct H1 as [Hlen1 Hrange1];
      destruct H2 as [Hlen2 Hrange2]
  | H1 : interval_int_range ?l1 |- _ =>
      let Hkeep1 := fresh "Hrange_keep" in
      let Hlen1 := fresh "Hlen" in
      let Hrange1 := fresh "Hrange" in
      pose proof H1 as Hkeep1;
      unfold interval_int_range in H1;
      destruct H1 as [Hlen1 Hrange1]
  end;
  repeat match goal with
  | H : forall i : Z, _ |- _ =>
      pose proof (H 0%Z ltac:(lia));
      pose proof (H 1%Z ltac:(lia));
      clear H
  end;
  unfold inter_len, inter_start, inter_end in *;
  entailer!;
  try nia.

Lemma proof_of_p127_intersection_safety_wit_5 : p127_intersection_safety_wit_5.
Proof.
  unfold p127_intersection_safety_wit_5.
  intros.
  prepare_127.
Qed.

Lemma proof_of_p127_intersection_safety_wit_6 : p127_intersection_safety_wit_6.
Proof.
  unfold p127_intersection_safety_wit_6.
  intros.
  prepare_127.
Qed.

Lemma proof_of_p127_intersection_safety_wit_7 : p127_intersection_safety_wit_7.
Proof.
  unfold p127_intersection_safety_wit_7.
  intros.
  prepare_127.
Qed.

Lemma proof_of_p127_intersection_safety_wit_8 : p127_intersection_safety_wit_8.
Proof.
  unfold p127_intersection_safety_wit_8.
  intros.
  prepare_127.
Qed.

Lemma proof_of_p127_intersection_safety_wit_12 : p127_intersection_safety_wit_12.
Proof.
  unfold p127_intersection_safety_wit_12.
  intros.
  prepare_127.
Qed.

Lemma proof_of_p127_intersection_entail_wit_1_1 : p127_intersection_entail_wit_1_1.
Proof.
  unfold p127_intersection_entail_wit_1_1.
  intros.
  prepare_127.
Qed.

Lemma proof_of_p127_intersection_entail_wit_1_2 : p127_intersection_entail_wit_1_2.
Proof.
  unfold p127_intersection_entail_wit_1_2.
  intros.
  prepare_127.
Qed.

Lemma proof_of_p127_intersection_entail_wit_1_3 : p127_intersection_entail_wit_1_3.
Proof.
  unfold p127_intersection_entail_wit_1_3.
  intros.
  prepare_127.
Qed.

Lemma proof_of_p127_intersection_entail_wit_1_4 : p127_intersection_entail_wit_1_4.
Proof.
  unfold p127_intersection_entail_wit_1_4.
  intros.
  prepare_127.
Qed.

Lemma proof_of_p127_intersection_entail_wit_2 : p127_intersection_entail_wit_2.
Proof.
  unfold p127_intersection_entail_wit_2.
  intros.
  prepare_127.
  apply prime_prefix_2.
Qed.

Lemma proof_of_p127_intersection_entail_wit_3 : p127_intersection_entail_wit_3.
Proof.
  unfold p127_intersection_entail_wit_3.
  intros.
  pre_process.
  subst.
  entailer!.
  entailer!.
  eapply prime_prefix_step; eauto.
Qed.

Lemma proof_of_p127_intersection_return_wit_1 : p127_intersection_return_wit_1.
Proof.
  unfold p127_intersection_return_wit_1.
  intros.
  pre_process.
  subst.
  entailer!.
  apply problem_127_spec_true.
  apply prime_len_true_from_prefix with (i := i); assumption.
Qed.

Lemma proof_of_p127_intersection_return_wit_2 : p127_intersection_return_wit_2.
Proof.
  unfold p127_intersection_return_wit_2.
  intros.
  pre_process.
  subst.
  entailer!.
  apply problem_127_spec_false.
  apply prime_len_false_divisor with (i := i); assumption.
Qed.

Lemma proof_of_p127_intersection_return_wit_3 : p127_intersection_return_wit_3.
Proof.
  unfold p127_intersection_return_wit_3.
  intros.
  pre_process.
  subst.
  entailer!.
  apply problem_127_spec_false.
  apply prime_len_false_small.
  lia.
Qed.

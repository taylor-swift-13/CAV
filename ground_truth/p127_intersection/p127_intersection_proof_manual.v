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
From SimpleC.EE.CAV.ground_truth_p127_intersection Require Import p127_intersection_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p127_intersection.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p127_intersection.v so public contract files expose definitions only. *)

Lemma prime_prefix_2 : forall n,
  prime_prefix 2 n.
Proof.
  unfold prime_prefix.
  intros n d H.
  lia.
Qed.
Lemma prime_prefix_step : forall i n,
  prime_prefix i n ->
  Z.rem n i <> 0 ->
  prime_prefix (i + 1) n.
Proof.
  unfold prime_prefix.
  intros i n Hpre Hmod d Hd.
  destruct (Z.eq_dec d i) as [-> | Hne].
  - exact Hmod.
  - apply Hpre. lia.
Qed.
Lemma prime_len_false_small : forall n,
  n < 2 ->
  ~ prime_len n.
Proof.
  unfold prime_len.
  intros n Hlt H.
  lia.
Qed.
Lemma prime_len_false_divisor : forall i n,
  2 <= i ->
  i * i <= n ->
  Z.rem n i = 0 ->
  ~ prime_len n.
Proof.
  unfold prime_len.
  intros i n Hi Hsquare Hmod [_ Hprime].
  specialize (Hprime i ltac:(lia)).
  contradiction.
Qed.
Lemma prime_len_true_from_prefix : forall i n,
  2 <= n ->
  2 <= i ->
  i * i > n ->
  prime_prefix i n ->
  prime_len n.
Proof.
  unfold prime_prefix, prime_len.
  intros i n Hn Hi Hexit Hpre.
  split.
  - assumption.
  - intros d [Hd Hsquare].
    apply Hpre.
    assert (d < i) by nia.
    lia.
Qed.
Lemma problem_127_spec_true : forall i1 i2,
  prime_len (inter_len i1 i2) ->
  problem_127_spec i1 i2 1.
Proof.
  intros i1 i2 Hprime_len.
  unfold problem_127_spec.
  left.
  split; [reflexivity |].
  split.
  - unfold inter_len in Hprime_len.
    destruct Hprime_len as [Hlen _].
    lia.
  - exact Hprime_len.
Qed.
Lemma problem_127_spec_false : forall i1 i2,
  ~ prime_len (inter_len i1 i2) ->
  problem_127_spec i1 i2 0.
Proof.
  intros i1 i2 Hnot.
  unfold problem_127_spec.
  right.
  split; [reflexivity |].
  right.
  exact Hnot.
Qed.
Lemma inter_len_range_safe : forall i1 i2,
  interval_int_range i1 ->
  interval_int_range i2 ->
  -2000000000 <= inter_len i1 i2 <= 2000000000.
Proof.
  intros i1 i2 [_ Hr1] [_ Hr2].
  unfold inter_len, inter_start, inter_end.
  pose proof (Hr1 0 ltac:(lia)).
  pose proof (Hr1 1 ltac:(lia)).
  pose proof (Hr2 0 ltac:(lia)).
  pose proof (Hr2 1 ltac:(lia)).
  nia.
Qed.
Lemma prime_loop_next_bound_127 : forall i n,
  2 <= i ->
  i <= 46340 ->
  n <= 2000000000 ->
  i * i <= n ->
  i + 1 <= 46340.
Proof.
  intros.
  nia.
Qed.


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

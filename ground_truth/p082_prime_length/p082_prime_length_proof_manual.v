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
From SimpleC.EE.CAV.ground_truth_p082_prime_length Require Import p082_prime_length_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p082_prime_length.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p082_prime_length.v so public contract files expose definitions only. *)

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
  - apply Hpre.
    lia.
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
  split; [assumption |].
  intros d [Hd Hsquare].
  apply Hpre.
  assert (d < i) by nia.
  lia.
Qed.
Lemma problem_82_spec_true : forall s,
  prime_len (Zlength s) ->
  problem_82_spec s 1.
Proof.
  intros s H.
  unfold problem_82_spec, bool_of.
  change (Z.eqb 1 1) with true.
  split; intros _; [exact H | reflexivity].
Qed.
Lemma problem_82_spec_false : forall s,
  ~ prime_len (Zlength s) ->
  problem_82_spec s 0.
Proof.
  intros s H.
  unfold problem_82_spec, bool_of.
  change (Z.eqb 0 1) with false.
  split; intros Hbad.
  - discriminate.
  - exfalso. apply H. exact Hbad.
Qed.
Lemma prime_loop_next_bound : forall i n,
  2 <= i ->
  i <= 46340 ->
  n <= 2147302921 ->
  i * i <= n ->
  i + 1 <= 46340.
Proof.
  intros.
  nia.
Qed.


Ltac prime82_pre :=
  pre_process;
  subst;
  entailer!;
  try nia.

Lemma proof_of_p082_prime_length_safety_wit_4 : p082_prime_length_safety_wit_4.
Proof.
  unfold p082_prime_length_safety_wit_4.
  intros.
  prime82_pre.
Qed. 

Lemma proof_of_p082_prime_length_entail_wit_1 : p082_prime_length_entail_wit_1.
Proof.
  unfold p082_prime_length_entail_wit_1.
  intros.
  pre_process.
  subst.
  entailer!.
  apply prime_prefix_2.
Qed. 

Lemma proof_of_p082_prime_length_entail_wit_2 : p082_prime_length_entail_wit_2.
Proof.
  unfold p082_prime_length_entail_wit_2.
  intros.
  pre_process.
  subst.
  entailer!.
  eapply prime_prefix_step; eauto.
Qed. 

Lemma proof_of_p082_prime_length_return_wit_1 : p082_prime_length_return_wit_1.
Proof.
  unfold p082_prime_length_return_wit_1.
  intros.
  pre_process.
  subst.
  entailer!.
  apply problem_82_spec_true.
  apply prime_len_true_from_prefix with (i := i); assumption.
Qed. 

Lemma proof_of_p082_prime_length_return_wit_2 : p082_prime_length_return_wit_2.
Proof.
  unfold p082_prime_length_return_wit_2.
  intros.
  pre_process.
  subst.
  entailer!.
  apply problem_82_spec_false.
  apply prime_len_false_divisor with (i := i); assumption.
Qed. 

Lemma proof_of_p082_prime_length_return_wit_3 : p082_prime_length_return_wit_3.
Proof.
  unfold p082_prime_length_return_wit_3.
  intros.
  pre_process.
  subst.
  entailer!.
  apply problem_82_spec_false.
  apply prime_len_false_small.
  lia.
Qed. 

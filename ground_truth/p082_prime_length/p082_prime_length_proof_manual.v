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
From SimpleC.EE.CAV.ground_truth_p082_prime_length Require Import p082_prime_length_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p082_prime_length.
Local Open Scope sac.

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

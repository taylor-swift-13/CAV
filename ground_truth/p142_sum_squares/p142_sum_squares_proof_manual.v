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
From SimpleC.EE.CAV.ground_truth_p142_sum_squares Require Import p142_sum_squares_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p142_sum_squares.
Local Open Scope sac.

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

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
From SimpleC.EE.CAV.ground_truth_p138_is_equal_to_sum_even Require Import p138_is_equal_to_sum_even_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p138_is_equal_to_sum_even.
Local Open Scope sac.

Lemma proof_of_p138_is_equal_to_sum_even_return_wit_1 : p138_is_equal_to_sum_even_return_wit_1.
Proof.
  unfold p138_is_equal_to_sum_even_return_wit_1; intros.
  pre_process; entailer!.
  unfold problem_138_spec.
  split; intro Hspec.
  - contradiction Hspec; reflexivity.
  - destruct Hspec as [Hge Hmod].
    pose proof (Z.rem_mod_nonneg n_pre 2 ltac:(lia) ltac:(lia)) as Hrem.
    rewrite <- Hrem in Hmod.
    contradiction.
Qed.

Lemma proof_of_p138_is_equal_to_sum_even_return_wit_2 : p138_is_equal_to_sum_even_return_wit_2.
Proof.
  unfold p138_is_equal_to_sum_even_return_wit_2; intros.
  pre_process; entailer!.
  unfold problem_138_spec.
  split; intro Hspec.
  - contradiction Hspec; reflexivity.
  - lia.
Qed.

Lemma proof_of_p138_is_equal_to_sum_even_return_wit_3 : p138_is_equal_to_sum_even_return_wit_3.
Proof.
  unfold p138_is_equal_to_sum_even_return_wit_3; intros.
  pre_process; entailer!.
  unfold problem_138_spec.
  split; intro Htmp.
  - split; [lia |].
    pose proof (Z.rem_mod_nonneg n_pre 2 ltac:(lia) ltac:(lia)) as Hrem.
    rewrite <- Hrem.
    assumption.
  - lia.
Qed.

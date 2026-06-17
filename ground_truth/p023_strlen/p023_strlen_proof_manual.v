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
From SimpleC.EE.CAV.ground_truth_p023_strlen Require Import p023_strlen_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p023_strlen.
Local Open Scope sac.

Lemma proof_of_p023_strlen_entail_wit_2 : p023_strlen_entail_wit_2.
Proof.
  unfold p023_strlen_entail_wit_2.
  intros.
  pre_process.
  assert (i < n).
  {
    eapply p023_nonzero_index_lt; try eassumption; lia.
  }
  entailer!.
Qed.

Lemma proof_of_p023_strlen_return_wit_1 : p023_strlen_return_wit_1.
Proof.
  unfold p023_strlen_return_wit_1.
  intros.
  pre_process.
  assert (i = n).
  {
    eapply p023_zero_index_eq; try eassumption; lia.
  }
  subst i.
  entailer!.
  unfold problem_23_spec.
  lia.
Qed.

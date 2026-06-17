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
From SimpleC.EE.CAV.ground_truth_p135_can_arrange Require Import p135_can_arrange_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p135_can_arrange.
Local Open Scope sac.

Lemma proof_of_p135_can_arrange_entail_wit_1 : p135_can_arrange_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  apply can_arrange_prefix_init.
  lia.
Qed.

Lemma proof_of_p135_can_arrange_entail_wit_2_1 : p135_can_arrange_entail_wit_2_1.
Proof.
  pre_process.
  entailer!.
  apply can_arrange_prefix_update with (max := max).
  - assumption.
  - lia.
  - apply can_arrange_hit_of_cond; lia.
Qed.

Lemma proof_of_p135_can_arrange_entail_wit_2_2 : p135_can_arrange_entail_wit_2_2.
Proof.
  pre_process.
  entailer!.
  apply can_arrange_prefix_keep.
  - assumption.
  - lia.
  - apply can_arrange_not_hit_of_cond; lia.
Qed.

Lemma proof_of_p135_can_arrange_return_wit_1 : p135_can_arrange_return_wit_1.
Proof.
  pre_process.
  replace i with arr_size_pre in * by lia.
  entailer!.
  apply can_arrange_prefix_full_spec.
  rewrite <- H2.
  assumption.
Qed.

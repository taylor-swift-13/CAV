Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260604_210529v_array_any_zero Require Import array_any_zero_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_array_any_zero_entail_wit_2 : array_any_zero_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  intros j Hj.
  destruct Hj as [Hj_lo Hj_hi].
  assert (j < i \/ j = i) as Hj_split by lia.
  destruct Hj_split as [Hj_lt | Hj_eq].
  - apply H3; lia.
  - subst j; auto.
Qed.

Lemma proof_of_array_any_zero_entail_wit_3 : array_any_zero_entail_wit_3.
Proof.
  pre_process.
  entailer!.
  intros j Hj.
  apply H2.
  lia.
Qed.

Lemma proof_of_array_any_zero_return_wit_1 : array_any_zero_return_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_array_any_zero_return_wit_2 : array_any_zero_return_wit_2.
Proof.
  pre_process.
  entailer!.
  intros _.
  exists i_3.
  lia.
Qed.

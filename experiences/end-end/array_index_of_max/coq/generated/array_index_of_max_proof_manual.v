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
From SimpleC.EE.CAV.verify_20260605_002002v_array_index_of_max Require Import array_index_of_max_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_array_index_of_max_entail_wit_2_1 : array_index_of_max_entail_wit_2_1.
Proof.
  pre_process.
  entailer!.
  + intros j Hj.
    specialize (H5 j Hj).
    lia.
  + intros j Hj.
    assert (j < i \/ j = i) by lia.
    destruct H9 as [Hlt | Heq].
    - specialize (H5 j ltac:(lia)).
      lia.
    - subst j. lia.
Qed.

Lemma proof_of_array_index_of_max_entail_wit_2_2 : array_index_of_max_entail_wit_2_2.
Proof.
  pre_process.
  entailer!.
  intros j Hj.
  assert (j < i \/ j = i) by lia.
  destruct H9 as [Hlt | Heq].
  - apply H5; lia.
  - subst j. lia.
Qed.

Lemma proof_of_array_index_of_max_return_wit_1 : array_index_of_max_return_wit_1.
Proof.
  pre_process.
  entailer!.
  intros j Hj.
  assert (i = n_pre) by lia.
  subst i.
  apply H4.
  lia.
Qed.

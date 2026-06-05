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
From SimpleC.EE.CAV.verify_20260605_002314v_array_index_of_min Require Import array_index_of_min_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_array_index_of_min_entail_wit_2_1 : array_index_of_min_entail_wit_2_1.
Proof.
  pre_process.
  entailer!.
  - intros j Hj.
    destruct Hj as [Hj0 Hjlt].
    assert (j < idx \/ idx <= j < i) as Hjcase by lia.
    destruct Hjcase as [Hjlt_idx | Hjmid].
    + assert (Znth idx l 0 <= Znth j l 0) by auto.
      lia.
    + assert (Znth idx l 0 <= Znth j l 0) by auto.
      lia.
  - intros j Hj.
    destruct Hj as [Hj0 Hjlt].
    assert (j < i \/ j = i) as Hjcase by lia.
    destruct Hjcase as [Hjlt_i | Hjeq].
    + assert (Znth idx l 0 <= Znth j l 0) by auto.
      lia.
    + subst j. lia.
Qed. 

Lemma proof_of_array_index_of_min_entail_wit_2_2 : array_index_of_min_entail_wit_2_2.
Proof.
  pre_process.
  entailer!.
  - intros j Hj.
    destruct Hj as [Hj0 Hjlt].
    assert (j < i \/ j = i) as Hjcase by lia.
    destruct Hjcase as [Hjlt_i | Hjeq].
    + auto.
    + subst j. lia.
Qed. 

Lemma proof_of_array_index_of_min_return_wit_1 : array_index_of_min_return_wit_1.
Proof.
  pre_process.
  assert (i = n_pre) by lia.
  subst i.
  entailer!.
Qed. 

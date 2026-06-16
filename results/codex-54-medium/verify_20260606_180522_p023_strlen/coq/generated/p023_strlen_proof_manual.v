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
From SimpleC.EE.CAV.verify_20260606_180522_p023_strlen Require Import p023_strlen_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p023_strlen.
Local Open Scope sac.

Lemma proof_of_p023_strlen_entail_wit_2 : p023_strlen_entail_wit_2.
Proof.
  pre_process.
  assert (Hi_lt : i < n).
  { destruct (Z_lt_ge_dec i n) as [Hlt | Hge]; auto.
    assert (i = n) by lia.
    subst i.
    exfalso.
    rewrite app_Znth2 in H by lia.
    replace (n - Zlength l) with 0 in H by lia.
    simpl in H.
    contradiction. }
  entailer!.
  intros k Hk.
  destruct (Z.eq_dec k i) as [Heq | Hneq].
  - subst k. apply H9. lia.
  - apply H4. lia.
Qed.

Lemma proof_of_p023_strlen_return_wit_1 : p023_strlen_return_wit_1.
Proof.
  pre_process.
  assert (Hi_eq : i = n).
  { destruct (Z_lt_ge_dec i n) as [Hi | Hi].
    - rewrite app_Znth1 in H by lia.
      specialize (H9 i ltac:(lia)).
      contradiction.
    - lia. }
  entailer!.
  unfold problem_23_spec.
  lia.
Qed.

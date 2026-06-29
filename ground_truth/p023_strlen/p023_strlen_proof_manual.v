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
From SimpleC.EE.CAV.ground_truth_p023_strlen Require Import p023_strlen_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p023_strlen.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p023_strlen.v so public contract files expose definitions only. *)

Lemma p023_nonzero_index_lt : forall l n i,
  Zlength l = n ->
  (forall k, 0 <= k /\ k < n -> Znth k l 0 <> 0) ->
  0 <= i ->
  i <= n ->
  Znth i (app l (cons 0 nil)) 0 <> 0 ->
  i < n.
Proof.
  intros l n i Hlen Hnz Hi Hle Hchar.
  rewrite <- Hlen in *.
  destruct (Z_lt_ge_dec i (Zlength l)) as [Hlt | Hge]; [exact Hlt |].
  assert (i = Zlength l) by lia.
  subst i.
  rewrite app_Znth2 in Hchar by lia.
  replace (Zlength l - Zlength l) with 0 in Hchar by lia.
  simpl in Hchar.
  contradiction.
Qed.
Lemma p023_zero_index_eq : forall l n i,
  Zlength l = n ->
  (forall k, 0 <= k /\ k < n -> Znth k l 0 <> 0) ->
  0 <= i ->
  i <= n ->
  Znth i (app l (cons 0 nil)) 0 = 0 ->
  i = n.
Proof.
  intros l n i Hlen Hnz Hi Hle Hchar.
  rewrite <- Hlen in *.
  destruct (Z_lt_ge_dec i (Zlength l)) as [Hlt | Hge].
  - rewrite app_Znth1 in Hchar by lia.
    specialize (Hnz i ltac:(lia)).
    contradiction.
  - lia.
Qed.


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

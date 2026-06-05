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
From SimpleC.EE.CAV.verify_20260605_004036v_array_none_zero Require Import array_none_zero_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_array_none_zero_entail_wit_2 : array_none_zero_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  intros k Hk.
  assert (k < i \/ k = i) as Hsplit by lia.
  destruct Hsplit as [Hlt | Heq].
  - match goal with
    | Hprefix : forall k : Z, ((0 <= k /\ k < i) -> Znth k l 0 <> 0) |- _ =>
        apply Hprefix
    end.
    lia.
  - subst k.
    match goal with
    | Hcur : Znth i l 0 <> 0 |- _ => exact Hcur
    end.
Qed.

Lemma proof_of_array_none_zero_return_wit_1 : array_none_zero_return_wit_1.
Proof.
  pre_process.
  entailer!.
  intros _ i Hi.
  match goal with
  | Hprefix : forall k : Z, ((0 <= k /\ k < i_3) -> Znth k l 0 <> 0) |- _ =>
      apply Hprefix
  end.
  lia.
Qed.

Lemma proof_of_array_none_zero_return_wit_2 : array_none_zero_return_wit_2.
Proof.
  pre_process.
  entailer!.
  intros _.
  exists i_3.
  split.
  - lia.
  - exact H.
Qed.

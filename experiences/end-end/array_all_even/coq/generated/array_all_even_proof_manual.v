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
From SimpleC.EE.CAV.verify_20260604_201124v_array_all_even Require Import array_all_even_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_array_all_even_entail_wit_2 : array_all_even_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  intros k Hk.
  destruct Hk as [Hk0 Hk1].
  assert (k < i \/ k = i) as Hcase by lia.
  destruct Hcase as [Hlt | Heq].
  - match goal with
      | Hprefix : forall k : Z, 0 <= k < i -> Znth k l 0 % 2 = 0 |- _ =>
          apply Hprefix; lia
    end.
  - subst k; auto.
Qed.

Lemma proof_of_array_all_even_return_wit_1 : array_all_even_return_wit_1.
Proof.
  pre_process.
  Right.
  entailer!.
  intros i_2 Hi_2.
  match goal with
    | Hprefix : forall k : Z, 0 <= k < i_3 -> Znth k l 0 % 2 = 0 |- _ =>
        apply Hprefix; lia
  end.
Qed.

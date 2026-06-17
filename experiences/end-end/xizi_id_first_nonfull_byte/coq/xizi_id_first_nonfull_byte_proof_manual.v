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
From SimpleC.EE.CAV.verify_20260603_190108v_xizi_id_first_nonfull_byte Require Import xizi_id_first_nonfull_byte_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_xizi_id_first_nonfull_byte_entail_wit_2 : xizi_id_first_nonfull_byte_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  intros j Hj.
  destruct Hj as [Hj0 Hjlt].
  assert (j < i \/ j = i) as Hsplit by lia.
  destruct Hsplit as [Hlt | Heq].
  - match goal with
    | Hpref : forall k : Z, 0 <= k < i -> Z.land (Znth k l 0) 255 = 255 |- _ =>
        apply Hpref; lia
    end.
  - subst j.
    match goal with
    | Hcur : Z.land (Znth i l 0) 255 = 255 |- _ => exact Hcur
    end.
Qed. 

Lemma proof_of_xizi_id_first_nonfull_byte_return_wit_1 : xizi_id_first_nonfull_byte_return_wit_1.
Proof.
  pre_process.
  Right.
  entailer!.
  intros i2 Hi2.
  match goal with
  | Hpref : forall j : Z, 0 <= j < i_3 -> Z.land (Znth j l 0) 255 = 255 |- _ =>
      apply Hpref; lia
  end.
Qed. 

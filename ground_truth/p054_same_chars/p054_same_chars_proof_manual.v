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
From SimpleC.EE.CAV.ground_truth_p054_same_chars Require Import p054_same_chars_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p054_same_chars.
Local Open Scope sac.

Ltac same_chars_pre :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia.

Ltac solve_no_zero_goal :=
  match goal with
  | Hnz : no_zero ?l |- forall k : Z, 0 <= k /\ k < ?n -> Znth k ?l 0 <> 0 =>
      intros k Hk;
      destruct Hnz as [_ Hforall];
      apply Hforall;
      lia
  | Hnz : no_zero ?l, Hlen : Zlength ?l = ?n
    |- Znth 0 ?l 0 <> 0 /\ Znth (?n - 1) ?l 0 <> 0 =>
      destruct Hnz as [Hpos Hforall];
      split; apply Hforall; lia
  | Hnz : no_zero ?l |- Znth 0 ?l 0 <> 0 =>
      destruct Hnz as [Hpos Hforall];
      apply Hforall;
      lia
  | Hnz : no_zero ?l, Hlen : Zlength ?l = ?n
    |- Znth (?n - 1) ?l 0 <> 0 =>
      destruct Hnz as [Hpos Hforall];
      apply Hforall;
      lia
  end.

Lemma proof_of_p054_same_chars_partial_solve_wit_1_pure : p054_same_chars_partial_solve_wit_1_pure.
Proof.
  pre_process.
  entailer!; try solve_no_zero_goal; try lia.
Qed.

Lemma proof_of_p054_same_chars_partial_solve_wit_2_pure : p054_same_chars_partial_solve_wit_2_pure.
Proof.
  pre_process.
  entailer!; try solve_no_zero_goal; try lia.
Qed.

Lemma proof_of_p054_same_chars_partial_solve_wit_4_pure : p054_same_chars_partial_solve_wit_4_pure.
Proof.
  pre_process.
  entailer!; try solve_no_zero_goal; try lia.
Qed.

Lemma proof_of_p054_same_chars_partial_solve_wit_6_pure : p054_same_chars_partial_solve_wit_6_pure.
Proof.
  pre_process.
  entailer!; try solve_no_zero_goal; try lia.
Qed.

Lemma proof_of_p054_same_chars_entail_wit_1 : p054_same_chars_entail_wit_1.
Proof.
  unfold p054_same_chars_entail_wit_1.
  intros.
  same_chars_pre.
  entailer!.
  apply same_chars_prefix_zero.
Qed. 

Lemma proof_of_p054_same_chars_entail_wit_2 : p054_same_chars_entail_wit_2.
Proof.
  unfold p054_same_chars_entail_wit_2.
  intros.
  same_chars_pre.
  entailer!.
  apply same_chars_prefix_step; try lia.
  assumption.
  assumption.
Qed. 

Lemma proof_of_p054_same_chars_entail_wit_3 : p054_same_chars_entail_wit_3.
Proof.
  unfold p054_same_chars_entail_wit_3.
  intros.
  same_chars_pre.
  assert (i = Zlength l0) by lia.
  subst i.
  entailer!.
  apply same_chars_prefix_zero.
Qed. 

Lemma proof_of_p054_same_chars_entail_wit_4 : p054_same_chars_entail_wit_4.
Proof.
  unfold p054_same_chars_entail_wit_4.
  intros.
  same_chars_pre.
  entailer!.
  apply same_chars_prefix_step; try lia.
  assumption.
  assumption.
Qed. 

Lemma proof_of_p054_same_chars_return_wit_1 : p054_same_chars_return_wit_1.
Proof.
  unfold p054_same_chars_return_wit_1.
  intros.
  same_chars_pre.
  assert (i = Zlength l1) by lia.
  subst i.
  entailer!; try solve_no_zero_goal.
  apply problem_54_spec_true; unfold same_chars_all; assumption.
Qed. 

Lemma proof_of_p054_same_chars_return_wit_2 : p054_same_chars_return_wit_2.
Proof.
  unfold p054_same_chars_return_wit_2.
  intros.
  same_chars_pre.
  entailer!; try solve_no_zero_goal.
  apply problem_54_spec_false_right with (i := i); try lia; try assumption.
Qed. 

Lemma proof_of_p054_same_chars_return_wit_3 : p054_same_chars_return_wit_3.
Proof.
  unfold p054_same_chars_return_wit_3.
  intros.
  same_chars_pre.
  entailer!; try solve_no_zero_goal.
  apply problem_54_spec_false_left with (i := i); try lia; try assumption.
Qed. 

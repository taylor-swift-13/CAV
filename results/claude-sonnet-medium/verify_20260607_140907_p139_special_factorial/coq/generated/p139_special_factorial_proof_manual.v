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
From SimpleC.EE.CAV.verify_20260607_140907_p139_special_factorial Require Import p139_special_factorial_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p139_special_factorial.
Local Open Scope sac.

Lemma proof_of_p139_special_factorial_safety_wit_4 : p139_special_factorial_safety_wit_4.
Proof.
  pre_process.
  split_pures.
  - dump_pre_spatial.
    assert (i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) by lia.
    destruct H6 as [H6 | [H6 | [H6 | [H6 | [H6 | [H6 | [H6 | H6]]]]]]];
    subst i;
    unfold factorial, factorial_fuel in H4;
    simpl in H4;
    nia.
  - dump_pre_spatial.
    assert (i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) by lia.
    destruct H6 as [H6 | [H6 | [H6 | [H6 | [H6 | [H6 | [H6 | H6]]]]]]];
    subst i;
    unfold factorial, factorial_fuel in H4;
    simpl in H4;
    nia.
Qed.

Lemma proof_of_p139_special_factorial_safety_wit_5 : p139_special_factorial_safety_wit_5.
Proof.
  pre_process.
  split_pures.
  - dump_pre_spatial.
    assert (i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) by lia.
    destruct H6 as [H6 | [H6 | [H6 | [H6 | [H6 | [H6 | [H6 | H6]]]]]]];
    subst i;
    unfold factorial, factorial_fuel in H4;
    unfold bfact_coq, bfact_fuel in H5;
    simpl in H4, H5;
    nia.
  - dump_pre_spatial.
    assert (i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) by lia.
    destruct H6 as [H6 | [H6 | [H6 | [H6 | [H6 | [H6 | [H6 | H6]]]]]]];
    subst i;
    unfold factorial, factorial_fuel in H4;
    unfold bfact_coq, bfact_fuel in H5;
    simpl in H4, H5;
    nia.
Qed.

Lemma proof_of_p139_special_factorial_entail_wit_1 : p139_special_factorial_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_p139_special_factorial_entail_wit_2 : p139_special_factorial_entail_wit_2.
Proof.
  unfold p139_special_factorial_entail_wit_2.
  intros.
  entailer!.
  - assert (i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) by lia.
    destruct H6 as [H6 | [H6 | [H6 | [H6 | [H6 | [H6 | [H6 | H6]]]]]]];
    subst i;
    unfold factorial, factorial_fuel in H4;
    unfold bfact_coq, bfact_fuel in H5;
    unfold factorial, factorial_fuel;
    unfold bfact_coq, bfact_fuel;
    simpl in H4, H5;
    simpl;
    nia.
  - assert (i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) by lia.
    destruct H6 as [H6 | [H6 | [H6 | [H6 | [H6 | [H6 | [H6 | H6]]]]]]];
    subst i;
    unfold factorial, factorial_fuel in H4;
    unfold factorial, factorial_fuel;
    simpl in H4;
    simpl;
    nia.
Qed.

Lemma proof_of_p139_special_factorial_return_wit_1 : p139_special_factorial_return_wit_1.
Proof.
  unfold p139_special_factorial_return_wit_1.
  intros.
  entailer!.
  unfold problem_139_spec.
  assert (i = n_pre + 1) by lia.
  rewrite H6 in H5.
  replace (n_pre + 1 - 1) with n_pre in H5 by lia.
  lia.
Qed.

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
From SimpleC.EE.CAV.verify_20260607_082527_p139_special_factorial Require Import p139_special_factorial_goal.
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
Qed.

Lemma proof_of_p139_special_factorial_safety_wit_5 : p139_special_factorial_safety_wit_5.
Proof.
  pre_process.
  subst fact bfact.
  split_pures.
  - dump_pre_spatial.
    assert (Hprod1 : factorial (i - 1) * i <= 40320).
    {
      destruct (Z.eq_dec i 1) as [->|Hi1]; [vm_compute; congruence|].
      destruct (Z.eq_dec i 2) as [->|Hi2]; [vm_compute; congruence|].
      destruct (Z.eq_dec i 3) as [->|Hi3]; [vm_compute; congruence|].
      destruct (Z.eq_dec i 4) as [->|Hi4]; [vm_compute; congruence|].
      destruct (Z.eq_dec i 5) as [->|Hi5]; [vm_compute; congruence|].
      destruct (Z.eq_dec i 6) as [->|Hi6]; [vm_compute; congruence|].
      destruct (Z.eq_dec i 7) as [->|Hi7]; [vm_compute; congruence|].
      assert (i = 8) by lia.
      subst i.
      vm_compute; congruence.
    }
    assert (Hprod2 : 0 <= factorial (i - 1) * i) by nia.
    assert (Hprod3 : bfact_coq (i - 1) * (factorial (i - 1) * i) <= 5056584744960000).
    {
      destruct (Z.eq_dec i 1) as [->|Hi1]; [vm_compute; congruence|].
      destruct (Z.eq_dec i 2) as [->|Hi2]; [vm_compute; congruence|].
      destruct (Z.eq_dec i 3) as [->|Hi3]; [vm_compute; congruence|].
      destruct (Z.eq_dec i 4) as [->|Hi4]; [vm_compute; congruence|].
      destruct (Z.eq_dec i 5) as [->|Hi5]; [vm_compute; congruence|].
      destruct (Z.eq_dec i 6) as [->|Hi6]; [vm_compute; congruence|].
      destruct (Z.eq_dec i 7) as [->|Hi7]; [vm_compute; congruence|].
      assert (i = 8) by lia.
      subst i.
      vm_compute; congruence.
    }
    lia.
  - dump_pre_spatial.
    nia.
Qed.

Lemma proof_of_p139_special_factorial_entail_wit_1 : p139_special_factorial_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_p139_special_factorial_entail_wit_2 : p139_special_factorial_entail_wit_2.
Proof.
  pre_process.
  subst fact bfact.
  assert (Hi : 1 <= i <= 8) by lia.
  assert (Hfact_eq : factorial (i - 1) * i = factorial (i + 1 - 1)).
  {
    destruct (Z.eq_dec i 1) as [->|Hi1]; [vm_compute; reflexivity|].
    destruct (Z.eq_dec i 2) as [->|Hi2]; [vm_compute; reflexivity|].
    destruct (Z.eq_dec i 3) as [->|Hi3]; [vm_compute; reflexivity|].
    destruct (Z.eq_dec i 4) as [->|Hi4]; [vm_compute; reflexivity|].
    destruct (Z.eq_dec i 5) as [->|Hi5]; [vm_compute; reflexivity|].
    destruct (Z.eq_dec i 6) as [->|Hi6]; [vm_compute; reflexivity|].
    destruct (Z.eq_dec i 7) as [->|Hi7]; [vm_compute; reflexivity|].
    assert (i = 8) by lia.
    subst i.
    vm_compute; reflexivity.
  }
  assert (Hbfact_eq : bfact_coq (i - 1) * (factorial (i - 1) * i) = bfact_coq (i + 1 - 1)).
  {
    destruct (Z.eq_dec i 1) as [->|Hi1]; [vm_compute; reflexivity|].
    destruct (Z.eq_dec i 2) as [->|Hi2]; [vm_compute; reflexivity|].
    destruct (Z.eq_dec i 3) as [->|Hi3]; [vm_compute; reflexivity|].
    destruct (Z.eq_dec i 4) as [->|Hi4]; [vm_compute; reflexivity|].
    destruct (Z.eq_dec i 5) as [->|Hi5]; [vm_compute; reflexivity|].
    destruct (Z.eq_dec i 6) as [->|Hi6]; [vm_compute; reflexivity|].
    destruct (Z.eq_dec i 7) as [->|Hi7]; [vm_compute; reflexivity|].
    assert (i = 8) by lia.
    subst i.
    vm_compute; reflexivity.
  }
  assert (Hfact_bound : factorial (i - 1) * i <= 40320).
  {
    destruct (Z.eq_dec i 1) as [->|Hi1]; [vm_compute; congruence|].
    destruct (Z.eq_dec i 2) as [->|Hi2]; [vm_compute; congruence|].
    destruct (Z.eq_dec i 3) as [->|Hi3]; [vm_compute; congruence|].
    destruct (Z.eq_dec i 4) as [->|Hi4]; [vm_compute; congruence|].
    destruct (Z.eq_dec i 5) as [->|Hi5]; [vm_compute; congruence|].
    destruct (Z.eq_dec i 6) as [->|Hi6]; [vm_compute; congruence|].
    destruct (Z.eq_dec i 7) as [->|Hi7]; [vm_compute; congruence|].
    assert (i = 8) by lia.
    subst i.
    vm_compute; congruence.
  }
  assert (Hbfact_bound : bfact_coq (i - 1) * (factorial (i - 1) * i) <= 5056584744960000).
  {
    destruct (Z.eq_dec i 1) as [->|Hi1]; [vm_compute; congruence|].
    destruct (Z.eq_dec i 2) as [->|Hi2]; [vm_compute; congruence|].
    destruct (Z.eq_dec i 3) as [->|Hi3]; [vm_compute; congruence|].
    destruct (Z.eq_dec i 4) as [->|Hi4]; [vm_compute; congruence|].
    destruct (Z.eq_dec i 5) as [->|Hi5]; [vm_compute; congruence|].
    destruct (Z.eq_dec i 6) as [->|Hi6]; [vm_compute; congruence|].
    destruct (Z.eq_dec i 7) as [->|Hi7]; [vm_compute; congruence|].
    assert (i = 8) by lia.
    subst i.
    vm_compute; congruence.
  }
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. exact H0.
    + dump_pre_spatial. exact H1.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact Hfact_eq.
    + dump_pre_spatial. exact Hbfact_eq.
    + dump_pre_spatial. nia.
    + dump_pre_spatial. exact Hfact_bound.
    + dump_pre_spatial. nia.
    + dump_pre_spatial. exact Hbfact_bound.
Qed.

Lemma proof_of_p139_special_factorial_return_wit_1 : p139_special_factorial_return_wit_1.
Proof.
  pre_process.
  assert (i = n_pre + 1) by lia.
  subst i.
  subst fact bfact.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold problem_139_spec.
    replace (n_pre + 1 - 1) with n_pre by lia.
    reflexivity.
Qed.

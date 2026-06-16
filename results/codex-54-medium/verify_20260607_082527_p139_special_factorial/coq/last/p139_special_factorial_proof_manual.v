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
From SimpleC.EE.humaneval Require Import p139_special_factorial_goal.
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
    assert (Hi8 : i <= 8) by lia.
    assert (Hprod1 : factorial (i - 1) * i <= 40320) by nia.
    assert (Hprod2 : 0 <= factorial (i - 1) * i) by nia.
    assert (Hprod3 : bfact_coq (i - 1) * (factorial (i - 1) * i) <= 5056584744960000) by nia.
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
  Show.
Qed.

Lemma proof_of_p139_special_factorial_return_wit_1 : p139_special_factorial_return_wit_1.
Proof.
  pre_process.
  unfold problem_139_spec.
  assert (i = n_pre + 1) by lia.
  subst i.
  subst fact bfact.
  assert (1 <= n_pre <= 8) by lia.
  destruct (Z.eq_dec n_pre 1) as [->|Hn1]; [vm_compute; reflexivity|].
  destruct (Z.eq_dec n_pre 2) as [->|Hn2]; [vm_compute; reflexivity|].
  destruct (Z.eq_dec n_pre 3) as [->|Hn3]; [vm_compute; reflexivity|].
  destruct (Z.eq_dec n_pre 4) as [->|Hn4]; [vm_compute; reflexivity|].
  destruct (Z.eq_dec n_pre 5) as [->|Hn5]; [vm_compute; reflexivity|].
  destruct (Z.eq_dec n_pre 6) as [->|Hn6]; [vm_compute; reflexivity|].
  destruct (Z.eq_dec n_pre 7) as [->|Hn7]; [vm_compute; reflexivity|].
  assert (n_pre = 8) by lia.
  subst n_pre.
  vm_compute; reflexivity.
Qed.

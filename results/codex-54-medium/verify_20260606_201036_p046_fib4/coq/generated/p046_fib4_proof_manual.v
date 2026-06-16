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
From SimpleC.EE.CAV.verify_20260606_201036_p046_fib4 Require Import p046_fib4_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p046_fib4.
Local Open Scope sac.

Lemma proof_of_p046_fib4_safety_wit_14 : p046_fib4_safety_wit_14.
Proof.
  pre_process.
  pose proof H4 i as Hr.
  assert (Hi_range : 4 <= i <= n_pre) by lia.
  specialize (Hr Hi_range).
  destruct Hr as [_ [_ Hr]].
  entailer!.
Qed.

Lemma proof_of_p046_fib4_safety_wit_15 : p046_fib4_safety_wit_15.
Proof.
  pre_process.
  pose proof H4 i as Hr.
  assert (Hi_range : 4 <= i <= n_pre) by lia.
  specialize (Hr Hi_range).
  destruct Hr as [_ [Hr _]].
  entailer!.
Qed.

Lemma proof_of_p046_fib4_safety_wit_16 : p046_fib4_safety_wit_16.
Proof.
  pre_process.
  pose proof H4 i as Hr.
  assert (Hi_range : 4 <= i <= n_pre) by lia.
  specialize (Hr Hi_range).
  destruct Hr as [Hr _].
  entailer!.
Qed.

Lemma proof_of_p046_fib4_safety_wit_17 : p046_fib4_safety_wit_17.
Proof.
  pre_process.
  pose proof H3 i as Hr.
  assert (Hi_range : 4 <= i <= n_pre) by lia.
  specialize (Hr Hi_range).
  destruct Hr as [_ [_ Hr]].
  entailer!.
Qed.

Lemma proof_of_p046_fib4_safety_wit_18 : p046_fib4_safety_wit_18.
Proof.
  pre_process.
  pose proof H3 i as Hr.
  assert (Hi_range : 4 <= i <= n_pre) by lia.
  specialize (Hr Hi_range).
  destruct Hr as [_ [Hr _]].
  entailer!.
Qed.

Lemma proof_of_p046_fib4_safety_wit_19 : p046_fib4_safety_wit_19.
Proof.
  pre_process.
  pose proof H3 i as Hr.
  assert (Hi_range : 4 <= i <= n_pre) by lia.
  specialize (Hr Hi_range).
  destruct Hr as [Hr _].
  entailer!.
Qed.

Lemma proof_of_p046_fib4_entail_wit_1 : p046_fib4_entail_wit_1.
Proof.
  pre_process.
  Right.
  simpl.
  split_pure_spatial.
  - cancel.
  - split_pures.
    1: dump_pre_spatial; lia.
    1: dump_pre_spatial; lia.
    1: dump_pre_spatial; lia.
    1: dump_pre_spatial; exact H5.
    1: dump_pre_spatial; exact H6.
    1: dump_pre_spatial; lia.
    all: entailer!.
Qed.

Lemma proof_of_p046_fib4_entail_wit_2_1 : p046_fib4_entail_wit_2_1.
Proof.
  pre_process.
  Left.
  Exists (((a + b) + c) + d).
  simpl.
  subst i.
  split_pure_spatial.
  - cancel.
  - split_pures; try (dump_pre_spatial; lia); try (dump_pre_spatial; assumption).
    entailer!.
    rewrite H6, H7, H8, H9.
    vm_compute.
    reflexivity.
Qed.

Lemma proof_of_p046_fib4_entail_wit_2_2 : p046_fib4_entail_wit_2_2.
Proof.
  pre_process.
  Left.
  Exists (((a + b) + c) + d).
  simpl.
  assert (Hi_nat : i = Z.of_nat (Z.to_nat i)) by lia.
  rewrite Hi_nat in H6, H7, H8, H9.
  rewrite Hi_nat.
  destruct (Z.to_nat i) as [| [| [| [| [| m]]]]] eqn:Hi; try lia.
  replace (Z.of_nat (S (S (S (S (S m))))) - 4) with (Z.of_nat (S m)) in H6 by lia.
  replace (Z.of_nat (S (S (S (S (S m))))) - 3) with (Z.of_nat (S (S m))) in H7 by lia.
  replace (Z.of_nat (S (S (S (S (S m))))) - 2) with (Z.of_nat (S (S (S m)))) in H8 by lia.
  replace (Z.of_nat (S (S (S (S (S m))))) - 1) with (Z.of_nat (S (S (S (S m))))) in H9 by lia.
  replace (Z.of_nat (S (S (S (S (S m))))) + 1 - 4) with (Z.of_nat (S (S m))) by lia.
  replace (Z.of_nat (S (S (S (S (S m))))) + 1 - 3) with (Z.of_nat (S (S (S m)))) by lia.
  replace (Z.of_nat (S (S (S (S (S m))))) + 1 - 2) with (Z.of_nat (S (S (S (S m))))) by lia.
  replace (Z.of_nat (S (S (S (S (S m))))) + 1 - 1) with (Z.of_nat (S (S (S (S (S m)))))) by lia.
  split_pure_spatial.
  - cancel.
  - split_pures; try (dump_pre_spatial; lia); try (dump_pre_spatial; assumption).
    entailer!.
    rewrite H6, H7, H8, H9.
    assert (Hm_bound_z : Z.of_nat m <= 95) by lia.
    assert (Hm_bound : (m <= 95)%nat).
    { apply Nat2Z.inj_le. lia. }
    clear H H0 H1 H2 H3 H4 H5 Hi Hi_nat Hm_bound_z.
    revert Hm_bound.
    do 96 (
      destruct m as [| m];
      [ intros _; vm_compute; reflexivity
      | simpl ]
    ).
    intros Hm_bound.
    lia.
Qed.

Lemma proof_of_p046_fib4_return_wit_1 : p046_fib4_return_wit_1.
Proof.
  pre_process.
  entailer!.
  assert (i = n_pre + 1) by lia.
  subst i.
  replace (n_pre + 1 - 1) with n_pre by lia.
  tauto.
Qed.

Lemma proof_of_p046_fib4_return_wit_2 : p046_fib4_return_wit_2.
Proof.
  pre_process.
  entailer!.
  assert (n_pre = 3) by lia.
  subst.
  cbv [problem_46_spec fib4 fib4_fuel].
  tauto.
Qed.

Lemma proof_of_p046_fib4_return_wit_3 : p046_fib4_return_wit_3.
Proof.
  pre_process.
  entailer!.
  subst.
  cbv [problem_46_spec fib4 fib4_fuel].
  tauto.
Qed.

Lemma proof_of_p046_fib4_return_wit_4 : p046_fib4_return_wit_4.
Proof.
  pre_process.
  entailer!.
  subst.
  cbv [problem_46_spec fib4 fib4_fuel].
  tauto.
Qed.

Lemma proof_of_p046_fib4_return_wit_5 : p046_fib4_return_wit_5.
Proof.
  pre_process.
  entailer!.
  subst.
  cbv [problem_46_spec fib4 fib4_fuel].
  tauto.
Qed.

Lemma proof_of_p046_fib4_return_wit_6 : p046_fib4_return_wit_6.
Proof.
  pre_process.
  entailer!.
  subst.
  cbv [problem_46_spec fib4 fib4_fuel].
  tauto.
Qed.

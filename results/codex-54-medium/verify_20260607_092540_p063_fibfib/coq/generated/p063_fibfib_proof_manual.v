Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260607_092540_p063_fibfib Require Import p063_fibfib_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p063_fibfib.
Local Open Scope sac.

Lemma fibfib_fuel_nat :
  forall fuel n,
    (n <= fuel)%nat ->
    fibfib_fuel fuel (Z.of_nat n) = Z.of_nat (fibfib_nat n).
Proof.
  induction fuel as [|fuel IH]; intros n Hle.
  - assert (n = 0)%nat by lia.
    subst n.
    reflexivity.
  - destruct n as [| [| [| n']]]; cbn [fibfib_fuel fibfib_nat]; try reflexivity.
    replace (Z.of_nat (S (S (S n'))) - 1) with (Z.of_nat (S (S n'))) by lia.
    replace (Z.of_nat (S (S (S n'))) - 2) with (Z.of_nat (S n')) by lia.
    replace (Z.of_nat (S (S (S n'))) - 3) with (Z.of_nat n') by lia.
    assert (Hz0 : (Z.of_nat (S (S (S n'))) =? 0)%Z = false) by (apply Z.eqb_neq; lia).
    assert (Hz1 : (Z.of_nat (S (S (S n'))) =? 1)%Z = false) by (apply Z.eqb_neq; lia).
    assert (Hz2 : (Z.of_nat (S (S (S n'))) =? 2)%Z = false) by (apply Z.eqb_neq; lia).
    rewrite Hz0, Hz1, Hz2.
    rewrite IH by lia.
    rewrite IH by lia.
    rewrite IH by lia.
    cbn [fibfib_nat].
    repeat rewrite Nat2Z.inj_add.
    lia.
Qed.

Lemma fibfib_of_nat :
  forall n,
    fibfib (Z.of_nat n) = Z.of_nat (fibfib_nat n).
Proof.
  intro n.
  unfold fibfib.
  rewrite Nat2Z.id.
  apply fibfib_fuel_nat.
  lia.
Qed.

Lemma fibfib_rec :
  forall i,
    3 <= i ->
    fibfib i = fibfib (i - 3) + fibfib (i - 2) + fibfib (i - 1).
Proof.
  intros i Hi.
  remember (Z.to_nat i) as n eqn:Hn.
  assert (Hi_nat : (3 <= n)%nat).
  {
    apply Nat2Z.inj_le.
    change (3 <= Z.of_nat n).
    subst n.
    rewrite Z2Nat.id by lia.
    lia.
  }
  assert (Hi_eq : i = Z.of_nat n).
  {
    subst n.
    rewrite Z2Nat.id by lia.
    reflexivity.
  }
  subst i.
  destruct n as [| [| [| n']]]; try lia.
  replace (Z.of_nat (S (S (S n'))) - 3) with (Z.of_nat n') by lia.
  replace (Z.of_nat (S (S (S n'))) - 2) with (Z.of_nat (S n')) by lia.
  replace (Z.of_nat (S (S (S n'))) - 1) with (Z.of_nat (S (S n'))) by lia.
  repeat rewrite fibfib_of_nat.
  simpl.
  repeat rewrite Nat2Z.inj_add.
  lia.
Qed.

Lemma proof_of_p063_fibfib_safety_wit_11 : p063_fibfib_safety_wit_11.
Proof.
  pre_process.
  subst a b c.
  split_pures.
  - dump_pre_spatial.
    unfold fibfib_step_int_range in H3.
    specialize (H3 i).
    assert (Hrange : 3 <= i <= n_pre) by lia.
    specialize (H3 Hrange).
    lia.
  - dump_pre_spatial.
    unfold fibfib_step_int_range in H3.
    specialize (H3 i).
    assert (Hrange : 3 <= i <= n_pre) by lia.
    specialize (H3 Hrange).
    lia.
Qed.

Lemma proof_of_p063_fibfib_safety_wit_12 : p063_fibfib_safety_wit_12.
Proof.
  pre_process.
  subst a b c.
  split_pures.
  - dump_pre_spatial.
    unfold fibfib_step_int_range in H3.
    specialize (H3 i).
    assert (Hrange : 3 <= i <= n_pre) by lia.
    specialize (H3 Hrange).
    lia.
  - dump_pre_spatial.
    unfold fibfib_step_int_range in H3.
    specialize (H3 i).
    assert (Hrange : 3 <= i <= n_pre) by lia.
    specialize (H3 Hrange).
    lia.
Qed.

Lemma proof_of_p063_fibfib_entail_wit_1 : p063_fibfib_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_p063_fibfib_entail_wit_2 : p063_fibfib_entail_wit_2.
Proof.
  pre_process.
  subst a b c.
  split_pure_spatial.
  - sep_apply store_int_undef_store_int.
    cancel.
  - split_pures.
    + dump_pre_spatial. exact H0.
    + dump_pre_spatial. exact H1.
    + dump_pre_spatial. exact H2.
    + dump_pre_spatial. exact H3.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      replace (i + 1 - 3) with (i - 2) by lia.
      reflexivity.
    + dump_pre_spatial.
      replace (i + 1 - 2) with (i - 1) by lia.
      reflexivity.
    + dump_pre_spatial.
      replace (i + 1 - 1) with i by lia.
      rewrite (fibfib_rec i) by lia.
      lia.
Qed.

Lemma proof_of_p063_fibfib_return_wit_1 : p063_fibfib_return_wit_1.
Proof.
  pre_process.
  assert (i = n_pre + 1) by lia.
  subst i.
  subst a b c.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold problem_63_spec.
    split; [lia|].
    replace (n_pre + 1 - 1) with n_pre by lia.
    reflexivity.
Qed.

Lemma proof_of_p063_fibfib_return_wit_2 : p063_fibfib_return_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold problem_63_spec.
    split; [lia|].
    subst n_pre.
    reflexivity.
Qed.

Lemma proof_of_p063_fibfib_return_wit_3 : p063_fibfib_return_wit_3.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold problem_63_spec.
    split; [lia|].
    subst n_pre.
    reflexivity.
Qed.

Lemma proof_of_p063_fibfib_return_wit_4 : p063_fibfib_return_wit_4.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold problem_63_spec.
    split; [lia|].
    subst n_pre.
    reflexivity.
Qed.

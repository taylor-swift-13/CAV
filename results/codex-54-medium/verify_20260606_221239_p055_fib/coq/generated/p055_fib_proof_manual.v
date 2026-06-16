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
From SimpleC.EE.CAV.verify_20260606_221239_p055_fib Require Import p055_fib_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p055_fib.
Local Open Scope sac.

Lemma fib_seq_0 : fib_seq 0 = 0.
Proof. reflexivity. Qed.

Lemma fib_seq_1 : fib_seq 1 = 1.
Proof. reflexivity. Qed.

Lemma fib_seq_2 : fib_seq 2 = 1.
Proof. reflexivity. Qed.

Lemma nat_ind2 (P : nat -> Prop) :
  P 0%nat ->
  P 1%nat ->
  (forall n, P n -> P (S n) -> P (S (S n))) ->
  forall n, P n.
Proof.
  intros H0 H1 Hstep.
  assert (forall n, P n /\ P (S n)) as Hpair.
  {
    fix IH 1.
    intros [| n].
    - split; [exact H0 | exact H1].
    - destruct (IH n) as [Hn HSn].
      split.
      + exact HSn.
      + apply Hstep; assumption.
  }
  intro n.
  destruct (Hpair n) as [Hn _].
  exact Hn.
Qed.

Lemma fib_seq_fuel_enough :
  forall k fuel, (k <= fuel)%nat -> fib_seq_fuel fuel (Z.of_nat k) = Z.of_nat (fib k).
Proof.
  apply (nat_ind2 (fun k => forall fuel, (k <= fuel)%nat -> fib_seq_fuel fuel (Z.of_nat k) = Z.of_nat (fib k))).
  - intros fuel _.
    destruct fuel; reflexivity.
  - intros [| fuel] Hle.
    + lia.
    + reflexivity.
  - intros k IHk IHSk fuel Hle.
    destruct fuel as [| fuel'].
    + lia.
    + cbn [fib_seq_fuel fib].
      destruct (Z.eqb_spec (Z.of_nat (S (S k))) 0); [lia |].
      destruct (Z.eqb_spec (Z.of_nat (S (S k))) 1); [lia |].
      replace (Z.of_nat (S (S k)) - 1) with (Z.of_nat (S k)) by lia.
      replace (Z.of_nat (S (S k)) - 2) with (Z.of_nat k) by lia.
      rewrite IHSk by lia.
      rewrite IHk by lia.
      destruct k; simpl.
      * lia.
      * rewrite !Nat2Z.inj_add.
        lia.
Qed.

Lemma fib_seq_as_nat : forall i, 0 <= i -> fib_seq i = Z.of_nat (fib (Z.to_nat i)).
Proof.
  intros i Hi.
  unfold fib_seq.
  set (k := Z.to_nat i).
  replace i with (Z.of_nat k).
  2:{
    subst k.
    rewrite Z2Nat.id by lia.
    reflexivity.
  }
  change (fib_seq_fuel k (Z.of_nat k) = Z.of_nat (fib k)).
  apply fib_seq_fuel_enough.
  lia.
Qed.

Lemma fib_seq_step : forall i, 2 <= i -> fib_seq i = fib_seq (i - 1) + fib_seq (i - 2).
Proof.
  intros i Hi.
  rewrite fib_seq_as_nat by lia.
  rewrite fib_seq_as_nat by lia.
  rewrite fib_seq_as_nat by lia.
  rewrite Z2Nat.inj_sub by lia.
  rewrite Z2Nat.inj_sub by lia.
  destruct (Z.to_nat i) as [| [| n]] eqn: HiNat; [lia | lia |].
  simpl.
  rewrite Nat2Z.inj_add.
  rewrite Nat.sub_0_r.
  ring.
Qed.

Lemma proof_of_p055_fib_safety_wit_4 : p055_fib_safety_wit_4.
Proof.
  pre_process.
  entailer!.
  all:
    assert (2 <= i) by lia;
    unfold fib_step_int_range in H4;
    pose proof (H4 i (conj H8 H)) as Hrange;
    lia.
Qed.

Lemma proof_of_p055_fib_safety_wit_5 : p055_fib_safety_wit_5.
Proof.
  pre_process.
  entailer!.
  all:
    assert (2 <= i) by lia;
    unfold fib_step_int_range in H3;
    pose proof (H3 i (conj H9 H)) as Hrange;
    lia.
Qed.

Lemma proof_of_p055_fib_entail_wit_1 : p055_fib_entail_wit_1.
Proof.
  pre_process.
  right.
  unfold undef_store_int in H3 |- *.
  unfold andp in H3 |- *; cbn in H3 |- *.
  destruct H3 as [Hvalid Hstore].
  unfold fib_step_int_range in H2.
  unfold isvalidptr_int in Hvalid.
  destruct Hvalid as [Haddr_nonneg [Haddr_bound Halign]].
  repeat split; try assumption; try reflexivity.
  - pose proof (H2 i H3) as Hrange.
    lia.
  - pose proof (H2 i H3) as Hrange.
    lia.
  - unfold coq_prop.
    lia.
Qed.

Lemma proof_of_p055_fib_entail_wit_2_1 : p055_fib_entail_wit_2_1.
Proof.
  pre_process.
  left.
  exists (a + b).
  unfold store_int in H8 |- *.
  unfold andp in H8 |- *; cbn in H8 |- *.
  destruct H8 as [Hpure Hstore].
  destruct Hpure as [Hvalid [Hmax Hmin]].
  unfold fib_step_int_range in H4.
  unfold isvalidptr_int in Hvalid.
  unfold coq_prop in *.
  destruct Hvalid as [Haddr_nonneg [Haddr_bound Halign]].
  repeat split; try assumption; try lia.
  - pose proof (H4 i0 H8) as Hrange.
    lia.
  - pose proof (H4 i0 H8) as Hrange.
    lia.
  - replace (i + 1 - 2) with (i - 1) by lia.
    exact H7.
  - replace (i + 1 - 1) with 2 by lia.
    rewrite H0 in H6, H7.
    rewrite H6, H7.
    vm_compute.
    lia.
  - replace (i + 1 - 1) with 2 by lia.
    rewrite H0 in H6, H7.
    rewrite H6, H7.
    vm_compute.
    lia.
Qed.

Lemma proof_of_p055_fib_entail_wit_2_2 : p055_fib_entail_wit_2_2.
Proof.
  pre_process.
  left.
  exists (a + b).
  unfold store_int in H9 |- *.
  unfold andp in H9 |- *; cbn in H9 |- *.
  destruct H9 as [Hpure Hstore].
  destruct Hpure as [Hvalid [Hmax Hmin]].
  unfold fib_step_int_range in H3.
  unfold isvalidptr_int in Hvalid.
  unfold coq_prop in *.
  destruct Hvalid as [Haddr_nonneg [Haddr_bound Halign]].
  repeat split; try assumption; try lia.
  - pose proof (H3 i0 H9) as Hrange.
    lia.
  - pose proof (H3 i0 H9) as Hrange.
    lia.
  - replace (i + 1 - 2) with (i - 1) by lia.
    exact H7.
  - replace (i + 1 - 1) with i by lia.
    rewrite H6, H7.
    rewrite (fib_seq_step i) by lia.
    lia.
  - replace (i + 1 - 1) with i by lia.
    rewrite H6, H7.
    rewrite (fib_seq_step i) by lia.
    lia.
Qed.

Lemma proof_of_p055_fib_return_wit_1 : p055_fib_return_wit_1.
Proof.
  pre_process.
  entailer!.
  unfold problem_55_spec.
  split; [lia |].
  replace n_pre with (i - 1) by lia.
  exact H7.
Qed.

Lemma proof_of_p055_fib_return_wit_2 : p055_fib_return_wit_2.
Proof.
  pre_process.
  entailer!.
  unfold problem_55_spec.
  split; [lia |].
  replace n_pre with (i - 1) by lia.
  exact H7.
Qed.

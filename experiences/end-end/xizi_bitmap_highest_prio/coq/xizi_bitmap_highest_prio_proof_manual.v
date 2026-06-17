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
From SimpleC.EE.CAV.verify_20260603_204428v_xizi_bitmap_highest_prio Require Import xizi_bitmap_highest_prio_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import xizi_bitmap_highest_prio.
Local Open Scope sac.

Lemma land1_eq0_testbit0_false :
  forall x : Z,
    Z.land x 1 = 0 ->
    Z.testbit x 0 = false.
Proof.
  intros x H.
  change 1 with (Z.ones 1) in H.
  rewrite Z.land_ones in H by lia.
  replace (2 ^ 1) with 2 in H by reflexivity.
  rewrite Z.bit0_eqb.
  rewrite H.
  reflexivity.
Qed.

Lemma shiftr_land1_eq0_testbit_false :
  forall x k : Z,
    0 <= k ->
    Z.land (Z.shiftr x k) 1 = 0 ->
    Z.testbit x k = false.
Proof.
  intros x k Hk H.
  apply land1_eq0_testbit0_false in H.
  rewrite Z.shiftr_spec in H by lia.
  replace (0 + k) with k in H by lia.
  exact H.
Qed.

Lemma testbit_false_land_shiftl_eq0 :
  forall x i : Z,
    0 <= i ->
    Z.testbit x i = false ->
    Z.land x (Z.shiftl 1 i) = 0.
Proof.
  intros x i Hi Hbit.
  apply Z.bits_inj_0.
  intro n.
  rewrite Z.land_spec.
  destruct (Z.eq_dec n i) as [-> | Hneq].
  - rewrite Hbit.
    reflexivity.
  - rewrite Z.shiftl_1_l.
    rewrite Z.pow2_bits_false by congruence.
    rewrite Bool.andb_false_r.
    reflexivity.
Qed.

Lemma testbit_false_shiftr_land1_eq0 :
  forall x k : Z,
    0 <= k ->
    Z.testbit x k = false ->
    Z.land (Z.shiftr x k) 1 = 0.
Proof.
  intros x k Hk Hbit.
  assert (Hbit0 : Z.testbit (Z.shiftr x k) 0 = false).
  { rewrite Z.shiftr_spec by lia.
    replace (0 + k) with k by lia.
    exact Hbit. }
  assert (Hzero : 0 <= 0) by lia.
  pose proof (testbit_false_land_shiftl_eq0 (Z.shiftr x k) 0 Hzero Hbit0) as Hland.
  replace (Z.shiftl 1 0) with 1 in Hland by reflexivity.
  exact Hland.
Qed.

Lemma land_shiftl_eq0_testbit_false :
  forall x i : Z,
    0 <= i ->
    Z.land x (Z.shiftl 1 i) = 0 ->
    Z.testbit x i = false.
Proof.
  intros x i Hi Hland.
  assert (Hbit : Z.testbit (Z.land x (Z.shiftl 1 i)) i = false).
  { rewrite Hland. apply Z.bits_0. }
  rewrite Z.land_spec in Hbit.
  rewrite Z.shiftl_1_l in Hbit.
  rewrite Z.pow2_bits_true in Hbit by lia.
  rewrite Bool.andb_true_r in Hbit.
  exact Hbit.
Qed.

Lemma land_shiftl_neq0_testbit_true :
  forall x i : Z,
    0 <= i ->
    Z.land x (Z.shiftl 1 i) <> 0 ->
    Z.testbit x i = true.
Proof.
  intros x i Hi Hnz.
  destruct (Z.testbit x i) eqn:Hbit; auto.
  exfalso.
  apply Hnz.
  apply testbit_false_land_shiftl_eq0; assumption.
Qed.

Lemma bitmap_zero_from_range_and_cleared_bits :
  forall bitmap_pre i : Z,
    i < 0 ->
    -1 <= i ->
    0 <= bitmap_pre ->
    bitmap_pre <= 2 ^ 32 - 1 ->
    (forall k : Z,
        i < k < 32 ->
        Z.land (Z.shiftr bitmap_pre k) 1 = 0) ->
    bitmap_pre = 0.
Proof.
  intros bitmap_pre i Hi_neg Hi_lo Hnonneg Hmax Hclear.
  apply Z.bits_inj_0.
  intro n.
  destruct (Z_lt_ge_dec n 0) as [Hnneg | Hnnonneg].
  - apply Z.testbit_neg_r; lia.
  - destruct (Z_lt_ge_dec n 32) as [Hnlt32 | Hnge32].
    + apply shiftr_land1_eq0_testbit_false with (k := n); try lia.
      apply Hclear; lia.
    + assert (Hltpow : bitmap_pre < 2 ^ 32) by lia.
      destruct (Z.eq_dec bitmap_pre 0) as [-> | Hnz].
      * apply Z.bits_0.
      * apply Z.bits_above_log2; try lia.
        assert (Hpos : 0 < bitmap_pre) by lia.
        assert (Hlog2lt32 : Z.log2 bitmap_pre < 32).
        { apply (proj1 (Z.log2_lt_pow2 bitmap_pre 32 Hpos)).
          exact Hltpow. }
        lia.
Qed.

Lemma proof_of_xizi_bitmap_highest_prio_entail_wit_3 : xizi_bitmap_highest_prio_entail_wit_3.
Proof.
  pre_process.
  entailer!.
  intros k Hk.
  assert (Hcase : k = i \/ i < k) by lia.
  destruct Hcase as [-> | Hik].
  - apply land_shiftl_eq0_testbit_false in H; try lia.
    apply testbit_false_shiftr_land1_eq0; try lia.
    exact H.
  - apply H5.
    lia.
Qed.

Lemma proof_of_xizi_bitmap_highest_prio_return_wit_1 : xizi_bitmap_highest_prio_return_wit_1.
Proof.
  pre_process.
  entailer!.
  left.
  split.
  - eapply bitmap_zero_from_range_and_cleared_bits; eauto; lia.
  - reflexivity.
Qed.

Lemma proof_of_xizi_bitmap_highest_prio_return_wit_2 : xizi_bitmap_highest_prio_return_wit_2.
Proof.
  pre_process.
  entailer!.
  unfold xizi_bitmap_highest_prio_spec.
  right.
  split.
  - lia.
  - split.
    + apply land_shiftl_neq0_testbit_true; lia.
    + intros k Hk.
      apply shiftr_land1_eq0_testbit_false with (k := k); try lia.
      apply H5; lia.
Qed.

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
From SimpleC.EE.CAV.verify_20260604_162058_add_digits Require Import add_digits_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import add_digits.
Local Open Scope sac.

Lemma digit_sum_fuel_nonpositive :
  forall fuel n, n <= 0 -> digit_sum_fuel n fuel = 0.
Proof.
  induction fuel; intros n Hn; simpl; auto.
  destruct (Z.leb n 0) eqn:Hleb; auto.
  apply Z.leb_gt in Hleb; lia.
Qed.

Lemma digit_sum_fuel_nonneg :
  forall fuel n, 0 <= n -> 0 <= digit_sum_fuel n fuel.
Proof.
  induction fuel; intros n Hn; simpl.
  - lia.
  - destruct (Z.leb n 0) eqn:Hleb.
    + lia.
    + apply Z.leb_gt in Hleb.
      assert (0 <= n % 10) by (apply Z.rem_nonneg; lia).
      assert (Hdiv_nonneg : 0 <= n / 10) by (apply Z.div_pos; lia).
      specialize (IHfuel (n / 10) Hdiv_nonneg).
      lia.
Qed.

Lemma div_10_lt_pos :
  forall n, 0 < n -> 0 <= n / 10 < n.
Proof.
  intros n Hn.
  assert (Hdiv_nonneg : 0 <= n / 10) by (apply Z.div_pos; lia).
  assert (Hdiv_lt : n / 10 < n).
  {
    apply Z.div_lt_upper_bound; lia.
  }
  lia.
Qed.

Lemma quot_10_lt_pos :
  forall n, 0 < n -> 0 <= n ÷ 10 < n.
Proof.
  intros n Hn.
  replace (n ÷ 10) with (n / 10).
  - apply div_10_lt_pos; lia.
  - symmetry. apply Z.quot_div_nonneg; lia.
Qed.

Lemma rem_10_bounds_pos :
  forall n, 0 < n -> 0 <= n % 10 <= n.
Proof.
  intros n Hn.
  assert (Hrem : 0 <= n % 10 < 10) by (apply Z.rem_bound_pos; lia).
  pose proof (Z.quot_pos n 10 ltac:(lia) ltac:(lia)) as Hq_nonneg.
  pose proof (Z.quot_rem n 10 ltac:(lia)) as Hdecomp.
  lia.
Qed.

Lemma digit_sum_fuel_stable :
  forall (fuel : nat) (n : Z) (extra : nat),
    0 <= n ->
    (Z.to_nat n <= fuel)%nat ->
    digit_sum_fuel n (fuel + extra)%nat = digit_sum_fuel n fuel.
Proof.
  intros fuel.
  induction fuel; intros n extra Hn Hfuel.
  - assert (n = 0) by lia.
    subst n. destruct extra; reflexivity.
  - simpl.
    destruct (Z.leb n 0) eqn:Hleb; auto.
    apply Z.leb_gt in Hleb.
    f_equal.
    rewrite (IHfuel (n / 10) extra).
    + reflexivity.
    + pose proof (div_10_lt_pos n Hleb) as [Hdiv_nonneg Hdiv_lt].
      lia.
    + pose proof (div_10_lt_pos n Hleb) as [Hdiv_nonneg Hdiv_lt].
      apply Nat2Z.inj_le.
      rewrite Z2Nat.id by lia.
      apply Nat2Z.inj_le in Hfuel.
      rewrite Nat2Z.inj_succ in Hfuel.
      rewrite Z2Nat.id in Hfuel by lia.
      lia.
Qed.

Lemma digit_sum_fuel_stable_ge :
  forall (n : Z) (fuel : nat),
    0 <= n ->
    (Z.to_nat n <= fuel)%nat ->
    digit_sum_fuel n fuel = digit_sum_z n.
Proof.
  intros n fuel Hn Hfuel.
  unfold digit_sum_z.
  assert (exists extra, fuel = (Z.to_nat n + extra)%nat) as [extra ->].
  {
    exists (fuel - Z.to_nat n)%nat.
    lia.
  }
  rewrite digit_sum_fuel_stable; auto.
Qed.

Lemma digit_sum_z_nonneg :
  forall n, 0 <= n -> 0 <= digit_sum_z n.
Proof.
  intros n Hn.
  unfold digit_sum_z.
  apply digit_sum_fuel_nonneg; lia.
Qed.

Lemma digit_sum_z_step :
  forall n,
    0 < n ->
    digit_sum_z n = Z.rem n 10 + digit_sum_z (n ÷ 10).
Proof.
  intros n Hn.
  unfold digit_sum_z at 1.
  assert (Hto : exists k, Z.to_nat n = S k).
  {
    destruct (Z.to_nat n) eqn:Hz; [lia | eauto].
  }
  destruct Hto as [k Hk].
  rewrite Hk. simpl.
  destruct (Z.leb n 0) eqn:Hleb.
  {
    apply Z.leb_le in Hleb; lia.
  }
  f_equal.
  replace (n / 10) with (n ÷ 10).
  - apply digit_sum_fuel_stable_ge.
    + pose proof (quot_10_lt_pos n Hn) as [Hq_nonneg Hq_lt].
      lia.
    + pose proof (quot_10_lt_pos n Hn) as [Hq_nonneg Hq_lt].
      assert (HkZ : Z.of_nat k = n - 1).
      {
        apply (f_equal Z.of_nat) in Hk.
        rewrite Nat2Z.inj_succ in Hk.
        rewrite Z2Nat.id in Hk by lia.
        lia.
      }
      apply Nat2Z.inj_le.
      rewrite Z2Nat.id by lia.
      lia.
  - apply Z.quot_div_nonneg; lia.
Qed.

Lemma digit_sum_fuel_le :
  forall fuel n, 0 <= n -> digit_sum_fuel n fuel <= n.
Proof.
  induction fuel; intros n Hn; simpl.
  - lia.
  - destruct (Z.leb n 0) eqn:Hleb.
    + apply Z.leb_le in Hleb; lia.
    + apply Z.leb_gt in Hleb.
      assert (Hdiv_nonneg : 0 <= n / 10) by (apply Z.div_pos; lia).
      specialize (IHfuel (n / 10) Hdiv_nonneg).
      assert (Hstep : n % 10 + digit_sum_fuel (n / 10) fuel <= n % 10 + n / 10).
      {
        apply Z.add_le_mono_l.
        exact IHfuel.
      }
      eapply Z.le_trans.
      * exact Hstep.
      * replace (n % 10) with (n mod 10) by (symmetry; apply Z.rem_mod_nonneg; lia).
        pose proof (Z.div_mod n 10 ltac:(lia)) as Hdecomp.
        lia.
Qed.

Lemma digit_sum_z_le_self :
  forall n, 0 <= n -> digit_sum_z n <= n.
Proof.
  intros n Hn.
  unfold digit_sum_z.
  apply digit_sum_fuel_le; lia.
Qed.

Lemma rem_10_le_digit_sum_z_pos :
  forall n, 0 < n -> n % 10 <= digit_sum_z n.
Proof.
  intros n Hn.
  rewrite (digit_sum_z_step n Hn).
  pose proof (digit_sum_z_nonneg (n ÷ 10)).
  assert (0 <= n ÷ 10) by (pose proof (quot_10_lt_pos n Hn); lia).
  specialize (H H0).
  lia.
Qed.

Lemma digit_sum_z_single_digit :
  forall n, 0 <= n < 10 -> digit_sum_z n = n.
Proof.
  intros n [Hn0 Hn10].
  destruct (Z.eq_dec n 0) as [-> | Hnz].
  - unfold digit_sum_z. reflexivity.
  - unfold digit_sum_z at 1.
    assert (Hto : exists k, Z.to_nat n = S k).
    {
      destruct (Z.to_nat n) eqn:Hz; [lia | eauto].
    }
    destruct Hto as [k Hk].
    rewrite Hk. simpl.
    destruct (Z.leb n 0) eqn:Hleb.
    + apply Z.leb_le in Hleb; lia.
    + replace (n / 10) with 0 by (symmetry; apply Z.div_small; lia).
      rewrite digit_sum_fuel_nonpositive by lia.
      rewrite Z.rem_small by lia.
      lia.
Qed.

Lemma digital_root_fuel_le_9 :
  forall fuel n, 0 <= n <= 9 -> digital_root_fuel n fuel = n.
Proof.
  induction fuel; intros n Hn; simpl; auto.
  destruct (Z.leb n 9) eqn:Hleb; auto.
  apply Z.leb_gt in Hleb; lia.
Qed.

Lemma digit_sum_z_lt_self_gt9 :
  forall n, 9 < n -> digit_sum_z n < n.
Proof.
  intros n Hn.
  rewrite (digit_sum_z_step n ltac:(lia)).
  assert (Hq_nonneg : 0 <= n ÷ 10) by (pose proof (quot_10_lt_pos n ltac:(lia)); lia).
  assert (Hq_ge_1 : 1 <= n ÷ 10).
  {
    replace (n ÷ 10) with (n / 10).
    - pose proof (Z.div_mod n 10 ltac:(lia)) as Hdecomp_div.
      pose proof (Z.mod_pos_bound n 10 ltac:(lia)) as Hmod.
      lia.
    - symmetry. apply Z.quot_div_nonneg; lia.
  }
  pose proof (digit_sum_z_le_self (n ÷ 10) Hq_nonneg) as Hsum_le.
  pose proof (Z.quot_rem n 10 ltac:(lia)) as Hdecomp.
  lia.
Qed.

Lemma digital_root_fuel_stable :
  forall (fuel : nat) (n : Z) (extra : nat),
    0 <= n ->
    (Z.to_nat n <= fuel)%nat ->
    digital_root_fuel n (fuel + extra)%nat = digital_root_fuel n fuel.
Proof.
  intros fuel.
  induction fuel; intros n extra Hn Hfuel.
  - assert (n = 0) by lia.
    subst n. destruct extra; reflexivity.
  - simpl.
    destruct (Z.leb n 9) eqn:Hleb; auto.
    apply Z.leb_gt in Hleb.
    rewrite (IHfuel (digit_sum_z n) extra).
    + reflexivity.
    + apply digit_sum_z_nonneg; lia.
    + pose proof (digit_sum_z_lt_self_gt9 n Hleb) as Hlt.
      apply Nat2Z.inj_le.
      rewrite Z2Nat.id by (apply digit_sum_z_nonneg; lia).
      apply Nat2Z.inj_le in Hfuel.
      rewrite Nat2Z.inj_succ in Hfuel.
      rewrite Z2Nat.id in Hfuel by lia.
      lia.
Qed.

Lemma digital_root_fuel_stable_ge :
  forall (n : Z) (fuel : nat),
    0 <= n ->
    (Z.to_nat n <= fuel)%nat ->
    digital_root_fuel n fuel = digital_root_z n.
Proof.
  intros n fuel Hn Hfuel.
  unfold digital_root_z.
  assert (exists extra, fuel = (Z.to_nat n + extra)%nat) as [extra ->].
  {
    exists (fuel - Z.to_nat n)%nat.
    lia.
  }
  rewrite digital_root_fuel_stable; auto.
Qed.

Lemma digital_root_z_single_digit :
  forall n, 0 <= n < 10 -> digital_root_z n = n.
Proof.
  intros n Hn.
  unfold digital_root_z.
  apply digital_root_fuel_le_9.
  lia.
Qed.

Lemma digital_root_z_step :
  forall n, 9 < n -> digital_root_z n = digital_root_z (digit_sum_z n).
Proof.
  intros n Hn.
  unfold digital_root_z at 1.
  assert (Hto : exists k, Z.to_nat n = S k).
  {
    destruct (Z.to_nat n) eqn:Hz; [lia | eauto].
  }
  destruct Hto as [k Hk].
  rewrite Hk. simpl.
  destruct (Z.leb n 9) eqn:Hleb.
  {
    apply Z.leb_le in Hleb; lia.
  }
  apply digital_root_fuel_stable_ge.
  - apply digit_sum_z_nonneg; lia.
  - pose proof (digit_sum_z_lt_self_gt9 n Hn) as Hlt.
    apply Nat2Z.inj_le.
    rewrite Z2Nat.id by (apply digit_sum_z_nonneg; lia).
    assert (HkZ : Z.of_nat k = n - 1).
    {
      apply (f_equal Z.of_nat) in Hk.
      rewrite Nat2Z.inj_succ in Hk.
      rewrite Z2Nat.id in Hk by lia.
      lia.
    }
    lia.
Qed.

Lemma proof_of_add_digits_safety_wit_4 : add_digits_safety_wit_4.
Proof.
  unfold add_digits_safety_wit_4.
  pre_process.
  entailer!.
  - pose proof (rem_10_bounds_pos num ltac:(lia)) as [Hrem_nonneg Hrem_le].
    lia.
  - pose proof (rem_10_le_digit_sum_z_pos num ltac:(lia)) as Hrem_le_sum.
    pose proof (digit_sum_z_le_self n0 ltac:(lia)) as Hsum_le_n0.
    assert (Hupper : sum + num % 10 <= digit_sum_z n0) by lia.
    assert (Hroot_bound : digit_sum_z n0 <= INT_MAX) by lia.
    eapply Z.le_trans.
    + exact Hupper.
    + exact Hroot_bound.
Qed. 

Lemma proof_of_add_digits_entail_wit_3 : add_digits_entail_wit_3.
Proof.
  unfold add_digits_entail_wit_3.
  pre_process.
  Exists num.
  entailer!.
Qed. 

Lemma proof_of_add_digits_entail_wit_4 : add_digits_entail_wit_4.
Proof.
  unfold add_digits_entail_wit_4.
  pre_process.
  Exists n0_2.
  entailer!.
  - match goal with
    | Hsum : sum + digit_sum_z num = digit_sum_z n0_2 |- _ =>
        rewrite <- Hsum;
        rewrite (digit_sum_z_step num ltac:(lia));
        lia
    end.
  - pose proof (quot_10_lt_pos num ltac:(lia)) as [Hq_nonneg Hq_lt].
    pose proof (rem_10_bounds_pos num ltac:(lia)) as [Hrem_nonneg Hrem_le].
    pose proof (rem_10_le_digit_sum_z_pos num ltac:(lia)) as Hrem_le_sum.
    pose proof (digit_sum_z_le_self n0_2 ltac:(lia)) as Hsum_le_n0.
    lia.
  - pose proof (rem_10_bounds_pos num ltac:(lia)) as [Hrem_nonneg Hrem_le].
    lia.
  - pose proof (quot_10_lt_pos num ltac:(lia)) as [Hq_nonneg Hq_lt].
    lia.
  - pose proof (quot_10_lt_pos num ltac:(lia)) as [Hq_nonneg Hq_lt].
    lia.
Qed. 

Lemma proof_of_add_digits_entail_wit_5 : add_digits_entail_wit_5.
Proof.
  unfold add_digits_entail_wit_5.
  pre_process.
  entailer!.
  assert (num = 0) by lia.
  subst num.
  replace (digit_sum_z 0) with 0 in H7 by (unfold digit_sum_z; reflexivity).
  assert (Hsum0 : sum = digit_sum_z n0) by lia.
  destruct (Z_le_gt_dec n0 9) as [Hsmall | Hlarge].
  - rewrite Hsum0.
    rewrite (digit_sum_z_single_digit n0) by lia.
    exact H6.
  - rewrite Hsum0.
    rewrite <- (digital_root_z_step n0) by lia.
    exact H6.
Qed. 

Lemma proof_of_add_digits_return_wit_1 : add_digits_return_wit_1.
Proof.
  unfold add_digits_return_wit_1.
  pre_process.
  entailer!.
  rewrite (digital_root_z_single_digit num) in H2 by lia.
  lia.
Qed. 

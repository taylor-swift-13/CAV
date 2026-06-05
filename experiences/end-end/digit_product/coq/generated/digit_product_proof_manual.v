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
From SimpleC.EE.CAV.verify_20260605_062321v_digit_product Require Import digit_product_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import digit_product.
Require Import digit_product_helper.
Local Open Scope sac.

Lemma div_10_lt_pos :
  forall n, 0 < n -> 0 <= n / 10 < n.
Proof.
  intros n Hn.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt; lia.
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

Lemma digit_product_loop_fuel_stable :
  forall (fuel : nat) (n acc : Z) (extra : nat),
    0 <= n ->
    (Z.to_nat n <= fuel)%nat ->
    digit_product_loop_fuel n acc (fuel + extra)%nat =
    digit_product_loop_fuel n acc fuel.
Proof.
  intros fuel.
  induction fuel; intros n acc extra Hn Hfuel.
  - assert (n = 0) by lia.
    subst n. destruct extra; reflexivity.
  - simpl.
    destruct (Z.leb n 0) eqn:Hleb; auto.
    apply Z.leb_gt in Hleb.
    pose proof (div_10_lt_pos n Hleb) as [Hdiv_nonneg Hdiv_lt].
    rewrite (IHfuel (n / 10) (acc * Z.rem n 10) extra).
    + reflexivity.
    + lia.
    + apply Nat2Z.inj_le.
      rewrite Z2Nat.id by lia.
      apply Nat2Z.inj_le in Hfuel.
      rewrite Nat2Z.inj_succ in Hfuel.
      rewrite Z2Nat.id in Hfuel by lia.
      lia.
Qed.

Lemma digit_product_loop_fuel_stable_ge :
  forall (n acc : Z) (fuel : nat),
    0 <= n ->
    (Z.to_nat n <= fuel)%nat ->
    digit_product_loop_fuel n acc fuel = digit_product_acc_z n acc.
Proof.
  intros n acc fuel Hn Hfuel.
  unfold digit_product_acc_z.
  assert (exists extra, fuel = (Z.to_nat n + extra)%nat) as [extra ->].
  {
    exists (fuel - Z.to_nat n)%nat.
    lia.
  }
  rewrite digit_product_loop_fuel_stable; auto.
Qed.

Lemma digit_product_safe_fuel_stable :
  forall (fuel : nat) (n acc : Z) (extra : nat),
    0 <= n ->
    (Z.to_nat n <= fuel)%nat ->
    digit_product_safe_fuel n acc (fuel + extra)%nat =
    digit_product_safe_fuel n acc fuel.
Proof.
  intros fuel.
  induction fuel; intros n acc extra Hn Hfuel.
  - assert (n = 0) by lia.
    subst n. destruct extra; reflexivity.
  - simpl.
    destruct (Z.leb n 0) eqn:Hleb; auto.
    apply Z.leb_gt in Hleb.
    pose proof (div_10_lt_pos n Hleb) as [Hdiv_nonneg Hdiv_lt].
    rewrite (IHfuel (n / 10) (acc * Z.rem n 10) extra).
    + reflexivity.
    + lia.
    + apply Nat2Z.inj_le.
      rewrite Z2Nat.id by lia.
      apply Nat2Z.inj_le in Hfuel.
      rewrite Nat2Z.inj_succ in Hfuel.
      rewrite Z2Nat.id in Hfuel by lia.
      lia.
Qed.

Lemma digit_product_safe_fuel_stable_ge :
  forall (n acc : Z) (fuel : nat),
    0 <= n ->
    (Z.to_nat n <= fuel)%nat ->
    digit_product_safe_fuel n acc fuel = digit_product_safe_z n acc.
Proof.
  intros n acc fuel Hn Hfuel.
  unfold digit_product_safe_z.
  assert (exists extra, fuel = (Z.to_nat n + extra)%nat) as [extra ->].
  {
    exists (fuel - Z.to_nat n)%nat.
    lia.
  }
  rewrite digit_product_safe_fuel_stable; auto.
Qed.

Lemma digit_product_acc_z_step :
  forall n acc,
    0 < n ->
    digit_product_acc_z n acc =
    digit_product_acc_z (n ÷ 10) (acc * (n % 10)).
Proof.
  intros n acc Hn.
  unfold digit_product_acc_z at 1.
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
  pose proof (quot_10_lt_pos n Hn) as [Hq_nonneg Hq_lt].
  replace (n / 10) with (n ÷ 10).
  - apply digit_product_loop_fuel_stable_ge; auto.
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

Lemma digit_product_safe_z_step :
  forall n acc,
    0 < n ->
    digit_product_safe_z n acc ->
    (-2147483648 <= acc * (n % 10) <= 2147483647) /\
    digit_product_safe_z (n ÷ 10) (acc * (n % 10)).
Proof.
  intros n acc Hn Hsafe.
  unfold digit_product_safe_z at 1 in Hsafe.
  assert (Hto : exists k, Z.to_nat n = S k).
  {
    destruct (Z.to_nat n) eqn:Hz; [lia | eauto].
  }
  destruct Hto as [k Hk].
  rewrite Hk in Hsafe. simpl in Hsafe.
  destruct (Z.leb n 0) eqn:Hleb.
  {
    apply Z.leb_le in Hleb; lia.
  }
  destruct Hsafe as [Hrange Hrec].
  split; [assumption|].
  pose proof (quot_10_lt_pos n Hn) as [Hq_nonneg Hq_lt].
  replace (n / 10) with (n ÷ 10) in Hrec by (apply Z.quot_div_nonneg; lia).
  replace (n / 10) with (n ÷ 10).
  - assert
      (Hstable :
         digit_product_safe_fuel (n ÷ 10) (acc * (n % 10)) k =
         digit_product_safe_z (n ÷ 10) (acc * (n % 10))).
    {
      apply digit_product_safe_fuel_stable_ge; auto.
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
    }
    rewrite <- Hstable.
    exact Hrec.
  - apply Z.quot_div_nonneg; lia.
Qed.

Lemma proof_of_digit_product_safety_wit_5 : digit_product_safety_wit_5.
Proof.
  unfold digit_product_safety_wit_5.
  pre_process.
  entailer!.
  all:
    match goal with
    | Hsafe : digit_product_safe_z ?n ?product |- _ =>
        pose proof (digit_product_safe_z_step n product ltac:(lia) Hsafe) as [Hrange _]
    end;
    change Int.min_signed with (-2147483648) in *;
    change Int.max_signed with 2147483647 in *;
    lia.
Qed.

Lemma proof_of_digit_product_entail_wit_1 : digit_product_entail_wit_1.
Proof.
  unfold digit_product_entail_wit_1.
  pre_process.
  entailer!.
  - unfold digit_product_acc_z, digit_product_z.
    destruct (Z.leb n_pre 0) eqn:Hleb.
    + apply Z.leb_le in Hleb. lia.
    + reflexivity.
  - unfold digit_product_pre_z in H1.
    tauto.
Qed.

Lemma proof_of_digit_product_entail_wit_2 : digit_product_entail_wit_2.
Proof.
  unfold digit_product_entail_wit_2.
  pre_process.
  entailer!.
  - rewrite <- H3.
    symmetry. apply digit_product_acc_z_step. lia.
  - pose proof (digit_product_safe_z_step n product ltac:(lia) H2) as [_ Hnext].
    exact Hnext.
  - pose proof (rem_10_bounds_pos n ltac:(lia)) as [Hrem_nonneg Hrem_le].
    nia.
  - apply Z.quot_pos; lia.
Qed.

Lemma proof_of_digit_product_return_wit_1 : digit_product_return_wit_1.
Proof.
  unfold digit_product_return_wit_1.
  pre_process.
  entailer!.
  assert (n = 0) by lia.
  subst n.
  match goal with
  | Hacc : digit_product_acc_z 0 product = digit_product_z n_pre |- _ =>
      replace (digit_product_acc_z 0 product) with product in Hacc
      by (unfold digit_product_acc_z; reflexivity)
  end.
  lia.
Qed.

Lemma proof_of_digit_product_return_wit_2 : digit_product_return_wit_2.
Proof.
  unfold digit_product_return_wit_2.
  pre_process.
  entailer!.
  subst n_pre.
  unfold digit_product_z.
  reflexivity.
Qed.

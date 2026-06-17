Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p094_skjkasdkd Require Import p094_skjkasdkd_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p094_skjkasdkd.
Local Open Scope sac.

Lemma proof_of_p094_skjkasdkd_safety_wit_10 : p094_skjkasdkd_safety_wit_10.
Proof.
  pre_process.
  assert (0 <= x <= INT_MAX) as Hxrange.
  {
    match goal with
    | Hx : x = Znth i lv 0,
      Hrange_all : list_nonneg_int_range lv |- _ =>
        rewrite Hx; apply Hrange_all; lia
    end.
  }
  match goal with
  | Hcond : j <= x ÷ j |- _ =>
      rewrite (Z.quot_div_nonneg x j) in Hcond by lia
  end.
  assert (x / j < x) by (apply Z.div_lt; lia).
  entailer!.
Qed.

Lemma proof_of_p094_skjkasdkd_safety_wit_11 : p094_skjkasdkd_safety_wit_11.
Proof.
  pre_process.
  assert (0 <= x <= INT_MAX) as Hxrange.
  {
    match goal with
    | Hx : x = Znth i lv 0,
      Hrange_all : list_nonneg_int_range lv |- _ =>
        rewrite Hx; apply Hrange_all; lia
    end.
  }
  match goal with
  | Hcond : j <= x ÷ j |- _ =>
      rewrite (Z.quot_div_nonneg x j) in Hcond by lia
  end.
  assert (x / j < x) by (apply Z.div_lt; lia).
  entailer!.
Qed.

Lemma proof_of_p094_skjkasdkd_safety_wit_18 : p094_skjkasdkd_safety_wit_18.
Proof.
  pre_process.
  match goal with
  | Hstate : digit_sum_state original_largest largest sum,
    Hpos : largest > 0 |- _ =>
      pose proof (digit_sum_state_step original_largest largest sum Hstate Hpos) as Hstep
  end.
  unfold digit_sum_state in Hstep.
  destruct Hstep as [_ [fuel [Hcur [Hsum [_ [Hbound _]]]]]].
  pose proof (sum_digits_fuel_nonneg (largest / 10) fuel) as Hnonneg.
  assert (sum + largest mod 10 <= sum + largest mod 10 + sum_digits_fuel (largest / 10) fuel) as Hstep_le by lia.
  assert (sum + largest mod 10 <= 100) as Hsum_le.
  { eapply Z.le_trans. exact Hstep_le. exact Hbound. }
  assert (largest % 10 = largest mod 10) as Hrem.
  { apply Z.rem_mod_nonneg; lia. }
  rewrite Hrem.
  entailer!.
Qed.

Lemma proof_of_p094_skjkasdkd_entail_wit_1 : p094_skjkasdkd_entail_wit_1.
Proof.
  unfold p094_skjkasdkd_entail_wit_1.
  intros.
  entailer!.
  - unfold digit_sum_int_range; lia.
  - apply largest_prime_prefix_init.
    rewrite <- H1; lia.
Qed.

Lemma proof_of_p094_skjkasdkd_entail_wit_2 : p094_skjkasdkd_entail_wit_2.
Proof.
  unfold p094_skjkasdkd_entail_wit_2.
  intros.
  entailer!.
  assert (0 <= Znth i lv 0 <= INT_MAX) as Hrange.
  {
    match goal with
    | Hrange_all: list_nonneg_int_range lv |- _ =>
        apply Hrange_all; lia
    end.
  }
  apply prime_scan_state_init; lia.
Qed.

Lemma proof_of_p094_skjkasdkd_entail_wit_3_1 : p094_skjkasdkd_entail_wit_3_1.
Proof.
  unfold p094_skjkasdkd_entail_wit_3_1.
  intros.
  entailer!.
  - eapply prime_scan_state_step_zero.
    + match goal with
      | Hs : prime_scan_state x j prime |- _ => exact Hs
      end.
    + match goal with
      | Hcond : j <= x ÷ j |- _ =>
          rewrite (Z.quot_div_nonneg x j) in Hcond by lia;
          exact Hcond
      end.
    + assert (x % (j) = x mod j) as Hrem.
      { apply Z.rem_mod_nonneg; lia. }
      rewrite <- Hrem.
      match goal with
      | Hmod : x % (j) = 0 |- _ => exact Hmod
      end.
  - match goal with
    | Hcond : j <= x ÷ j |- _ =>
        rewrite (Z.quot_div_nonneg x j) in Hcond by lia
    end.
    assert (x / j <= x) by (apply Z.div_le_upper_bound; nia).
    lia.
Qed.

Lemma proof_of_p094_skjkasdkd_entail_wit_3_2 : p094_skjkasdkd_entail_wit_3_2.
Proof.
  unfold p094_skjkasdkd_entail_wit_3_2.
  intros.
  entailer!.
  - eapply prime_scan_state_step_keep.
    + match goal with
      | Hs : prime_scan_state x j prime |- _ => exact Hs
      end.
    + match goal with
      | Hcond : j <= x ÷ j |- _ =>
          rewrite (Z.quot_div_nonneg x j) in Hcond by lia;
          exact Hcond
      end.
    + assert (x % (j) = x mod j) as Hrem.
      { apply Z.rem_mod_nonneg; lia. }
      intro Hmod.
      match goal with
      | Hnz : x % (j) <> 0 |- _ =>
          apply Hnz;
          rewrite Hrem;
          exact Hmod
      end.
  - match goal with
    | Hcond : j <= x ÷ j |- _ =>
        rewrite (Z.quot_div_nonneg x j) in Hcond by lia
    end.
    assert (x / j <= x) by (apply Z.div_le_upper_bound; nia).
    lia.
Qed.

Lemma proof_of_p094_skjkasdkd_entail_wit_4_1 : p094_skjkasdkd_entail_wit_4_1.
Proof.
  unfold p094_skjkasdkd_entail_wit_4_1.
  intros.
  entailer!.
  - assert (0 <= x <= INT_MAX) as Hrange.
    {
      subst x.
      match goal with
      | Hrange_all: list_nonneg_int_range lv |- _ =>
          apply Hrange_all; lia
      end.
    }
    exact Hrange.
  - assert (0 <= x <= INT_MAX) as Hrange.
    {
      subst x.
      match goal with
      | Hrange_all: list_nonneg_int_range lv |- _ =>
          apply Hrange_all; lia
      end.
    }
    eapply largest_prime_prefix_update.
    + match goal with
      | Hpref : largest_prime_prefix i lv largest |- _ => exact Hpref
      end.
    + lia.
    + match goal with
      | Hx : x = Znth i lv 0 |- _ => exact Hx
      end.
    + exact Hrange.
    + eapply prime_scan_state_exit_prime.
      * match goal with
        | Hs : prime_scan_state x j prime |- _ => exact Hs
        end.
      * match goal with
        | Hnz : prime <> 0 |- _ => exact Hnz
        end.
      * match goal with
        | Hexit : j > x ÷ j |- _ =>
            rewrite (Z.quot_div_nonneg x j) in Hexit by lia;
            exact Hexit
        end.
    + lia.
Qed.

Lemma proof_of_p094_skjkasdkd_entail_wit_4_2 : p094_skjkasdkd_entail_wit_4_2.
Proof.
  unfold p094_skjkasdkd_entail_wit_4_2.
  intros.
  entailer!.
  apply largest_prime_prefix_skip_not_prime; auto; try lia.
  match goal with
  | Hx: x = Znth i lv 0,
    Hz: prime = 0,
    Hs: prime_scan_state x j prime |- _ =>
      subst x; rewrite Hz in Hs; eapply prime_scan_state_zero_not_prime; exact Hs
  end.
Qed.

Lemma proof_of_p094_skjkasdkd_entail_wit_4_3 : p094_skjkasdkd_entail_wit_4_3.
Proof.
  unfold p094_skjkasdkd_entail_wit_4_3.
  intros.
  entailer!.
  apply largest_prime_prefix_skip_le; auto; lia.
Qed.

Lemma proof_of_p094_skjkasdkd_entail_wit_4_4 : p094_skjkasdkd_entail_wit_4_4.
Proof.
  unfold p094_skjkasdkd_entail_wit_4_4.
  intros.
  entailer!.
  apply largest_prime_prefix_skip_not_prime; auto; try lia.
  intro Hprime.
  pose proof (prime_gt_1_94 _ Hprime).
  lia.
Qed.

Lemma proof_of_p094_skjkasdkd_entail_wit_5 : p094_skjkasdkd_entail_wit_5.
Proof.
  pre_process.
  Exists largest.
  entailer!.
  - apply digit_sum_state_init; auto.
  - replace lst_size_pre with i by lia.
    exact H7.
Qed.

Lemma proof_of_p094_skjkasdkd_entail_wit_6 : p094_skjkasdkd_entail_wit_6.
Proof.
  pre_process.
  Exists original_largest_2.
  entailer!.
  assert (largest ÷ 10 = largest / 10) as Hquot.
  { apply Z.quot_div_nonneg; lia. }
  assert (largest % 10 = largest mod 10) as Hrem.
  { apply Z.rem_mod_nonneg; lia. }
  rewrite Hquot, Hrem.
  apply digit_sum_state_step; auto.
Qed.

Lemma proof_of_p094_skjkasdkd_return_wit_1 : p094_skjkasdkd_return_wit_1.
Proof.
  pre_process.
  assert (largest = 0).
  {
    unfold digit_sum_state in H8.
    destruct H8 as [_ [fuel [Hcur _]]].
    lia.
  }
  subst largest.
  entailer!.
  eapply problem_94_spec_of_digit_state.
  - exact H4.
  - rewrite H2 in H6. exact H6.
  - exact H7.
  - exact H8.
Qed.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import p146_specialFilter_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Lists.List Coq.ZArith.ZArith.

Import naive_C_Rules.
Require Import p146_specialFilter.
Local Open Scope sac.
Require Import Coq.ZArith.Zquot.
Require Import Lia.
From AUXLib Require Import ListLib.

Local Open Scope list_scope.

(* Proof helpers moved from p146_specialFilter.v so public contract files expose definitions only. *)

Lemma special_filter_prefix_0 : forall nums,
  special_filter_prefix 0 nums 0.
Proof.
  intros nums.
  unfold special_filter_prefix.
  rewrite Zsublist_nil by lia.
  simpl.
  split.
  - split; [lia | rewrite Zlength_correct; lia].
  - reflexivity.
Qed.
Lemma special_filter_prefix_snoc_special : forall nums i count,
  special_filter_prefix i nums count ->
  0 <= i < Zlength nums ->
  special_number_c (Znth i nums 0) ->
  special_filter_prefix (i + 1) nums (count + 1).
Proof.
  intros nums i count [Hbounds Hcount] Hi Hspecial.
  unfold special_filter_prefix in *.
  split; [lia|].
  rewrite (sublist_split 0 (i + 1) i nums)
    by lia.
  rewrite (sublist_single 0 i nums) by lia.
  rewrite filter_app.
  simpl.
  rewrite Hspecial.
  rewrite app_length.
  simpl.
  rewrite Hcount.
  lia.
Qed.
Lemma special_filter_prefix_snoc_not_special : forall nums i count,
  special_filter_prefix i nums count ->
  0 <= i < Zlength nums ->
  not_special_number_c (Znth i nums 0) ->
  special_filter_prefix (i + 1) nums count.
Proof.
  intros nums i count [Hbounds Hcount] Hi Hspecial.
  unfold special_filter_prefix in *.
  split; [lia|].
  rewrite (sublist_split 0 (i + 1) i nums)
    by lia.
  rewrite (sublist_single 0 i nums) by lia.
  rewrite filter_app.
  simpl.
  rewrite Hspecial.
  rewrite app_length.
  simpl.
  rewrite Nat.add_0_r.
  assumption.
Qed.
Lemma count_special_numbers_filter_length : forall nums,
  count_special_numbers nums =
  Z.of_nat (length (filter special_number_b nums)).
Proof.
  induction nums as [|x xs IH]; simpl.
  - reflexivity.
  - destruct (special_number_b x) eqn:Hx.
    + rewrite IH.
      change (length (x :: filter special_number_b xs))
        with (S (length (filter special_number_b xs))).
      rewrite Nat2Z.inj_succ.
      lia.
    + exact IH.
Qed.
Lemma problem_146_spec_of_prefix_full : forall nums out,
  special_filter_prefix (Zlength nums) nums out ->
  problem_146_spec nums out.
Proof.
  intros nums out [_ Hout].
  unfold problem_146_spec.
  rewrite count_special_numbers_filter_length.
  rewrite sublist_self in Hout by reflexivity.
  exact Hout.
Qed.
Lemma special_filter_prefix_count_bounds : forall i nums count,
  special_filter_prefix i nums count ->
  0 <= count <= i.
Proof.
  intros i nums count [Hi Hcount].
  subst count.
  split.
  - apply Nat2Z.is_nonneg.
  - assert (Hfilter :
        Z.of_nat (length (filter special_number_b (sublist 0 i nums))) <=
        Z.of_nat (length (sublist 0 i nums))).
    {
      apply Nat2Z.inj_le.
      induction (sublist 0 i nums) as [|x xs IH]; simpl.
      - lia.
      - destruct (special_number_b x); simpl; lia.
    }
    rewrite sublist_length in Hfilter.
    + rewrite Z2Nat.id in Hfilter by lia.
      lia.
    + lia.
    + destruct Hi as [_ Hi].
      exact Hi.
Qed.
Lemma special_scalar_int_range_of_list : forall nums i,
  special_filter_int_range nums ->
  0 <= i < Zlength nums ->
  special_scalar_int_range (Znth i nums 0).
Proof.
  intros nums i Hrange Hi.
  apply Hrange; assumption.
Qed.
Lemma first_digit_state_init : forall x,
  0 <= x ->
  first_digit_state x x.
Proof.
  intros x Hx.
  unfold first_digit_state.
  exists (Z.to_nat x).
  split; [lia|].
  split.
  - rewrite Z2Nat.id by lia.
    apply Z.pow_gt_lin_r; lia.
  - reflexivity.
Qed.
Lemma msd_fuel_small : forall fuel n,
  0 <= n < 10 ->
  msd_fuel fuel n = n.
Proof.
  induction fuel; intros n Hn; simpl.
  - rewrite Z.mod_small by lia. reflexivity.
  - destruct (Z_lt_dec n 10); lia.
Qed.
Lemma first_digit_value_small : forall n,
  0 <= n < 10 ->
  first_digit_value n = n.
Proof.
  intros n Hn.
  unfold first_digit_value.
  apply msd_fuel_small; assumption.
Qed.
Lemma first_digit_state_step : forall original current,
  first_digit_state original current ->
  10 <= current ->
  first_digit_state original (current ÷ 10).
Proof.
  intros original current [fuel [Hrange [Hpow Hval]]] Hcur.
  destruct fuel as [|fuel].
  - simpl in Hpow. lia.
  - unfold first_digit_state.
    exists fuel.
    split.
    + rewrite Z.quot_div_nonneg by lia.
      pose proof (Z.div_pos current 10 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound current 10 current ltac:(lia) ltac:(nia)).
      lia.
    + split.
      * rewrite Z.quot_div_nonneg by lia.
        apply Z.div_lt_upper_bound; try lia.
        replace (10 ^ Z.of_nat (S fuel)) with (10 * 10 ^ Z.of_nat fuel) in Hpow
          by (rewrite Nat2Z.inj_succ; rewrite Z.pow_succ_r by lia; reflexivity).
        exact Hpow.
      * rewrite Hval.
        simpl.
        destruct (Z_lt_dec current 10); [lia|].
        rewrite Z.quot_div_nonneg by lia.
        reflexivity.
Qed.
Lemma last_digit_rem_bounds : forall x,
  0 < x ->
  0 <= x % 10 <= 9.
Proof.
  intros x Hx.
  rewrite Z.rem_mod_nonneg by lia.
  pose proof (Z.mod_pos_bound x 10 ltac:(lia)).
  lia.
Qed.
Lemma odd_rem_iff_odd : forall n,
  0 <= n ->
  (n % 2 = 1 <-> Z.odd n = true).
Proof.
  intros n Hn.
  rewrite Z.rem_mod_nonneg by lia.
  rewrite Zmod_odd.
  destruct (Z.odd n); split; intros H; try reflexivity; try discriminate.
Qed.
Lemma special_number_intro_from_digits : forall x first last,
  10 < x ->
  first_digit_state x first ->
  0 <= first < 10 ->
  0 <= last <= 9 ->
  last = x % 10 ->
  first % 2 = 1 ->
  last % 2 = 1 ->
  special_number_c x.
Proof.
  intros x first last Hx [fuel [Hfr [Hpow Hfv]]] Hfirst Hlast_range Hlast Hfirst_odd Hlast_odd.
  assert (Hfirst_bool : Z.odd (msd_fuel fuel first) = true).
  {
    rewrite msd_fuel_small by lia.
    destruct (odd_rem_iff_odd first ltac:(lia)) as [H _].
    apply H in Hfirst_odd.
    exact Hfirst_odd.
  }
  assert (Hlast_bool : Z.odd (last_digit x) = true).
  {
    unfold last_digit.
    replace (Z.abs x) with x by lia.
    rewrite <- Z.rem_mod_nonneg by lia.
    rewrite Z.abs_eq.
    - destruct (odd_rem_iff_odd last ltac:(lia)) as [H _].
      apply H in Hlast_odd.
      rewrite Hlast in Hlast_odd.
      exact Hlast_odd.
    - pose proof (last_digit_rem_bounds x ltac:(lia)).
      lia.
  }
  unfold special_number_c, special_number_b, first_digit_value in *.
  rewrite Z.abs_eq by lia.
  apply andb_true_intro.
  split.
  - apply andb_true_intro.
    split.
    + apply Z.ltb_lt; lia.
    + rewrite Hfv. exact Hfirst_bool.
  - exact Hlast_bool.
Qed.
Lemma special_number_false_of_le10 : forall x,
  x <= 10 ->
  not_special_number_c x.
Proof.
  intros x Hx.
  unfold not_special_number_c, special_number_b.
  destruct (10 <? x) eqn:Hlt; [apply Z.ltb_lt in Hlt; lia|reflexivity].
Qed.
Lemma special_number_false_first_even : forall x first last,
  10 < x ->
  first_digit_state x first ->
  0 <= first < 10 ->
  0 <= last <= 9 ->
  last = x % 10 ->
  first % 2 <> 1 ->
  not_special_number_c x.
Proof.
  intros x first last Hx [fuel [Hfr [Hpow Hfv]]] Hfirst Hlast_range Hlast Hfirst_even.
  unfold not_special_number_c, special_number_b, first_digit_value in *.
  rewrite Z.abs_eq by lia.
  replace (10 <? x) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite Hfv.
  rewrite msd_fuel_small by lia.
  destruct (Z.odd first) eqn:Hodd; [|reflexivity].
  exfalso.
  apply Hfirst_even.
  destruct (odd_rem_iff_odd first ltac:(lia)) as [_ H].
  apply H; exact Hodd.
Qed.
Lemma special_number_false_last_even : forall x first last,
  10 < x ->
  first_digit_state x first ->
  0 <= first < 10 ->
  0 <= last <= 9 ->
  last = x % 10 ->
  last % 2 <> 1 ->
  not_special_number_c x.
Proof.
  intros x first last Hx [fuel [Hfr [Hpow Hfv]]] Hfirst Hlast_range Hlast Hlast_even.
  unfold not_special_number_c, special_number_b, first_digit_value in *.
  rewrite Z.abs_eq by lia.
  replace (10 <? x) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite Hfv.
  rewrite msd_fuel_small by lia.
  destruct (Z.odd first) eqn:Hfirst_odd; [|reflexivity].
  unfold last_digit.
  rewrite <- Z.rem_mod_nonneg by lia.
  rewrite Z.abs_eq.
  - rewrite <- Hlast.
    destruct (Z.odd last) eqn:Hodd; [|reflexivity].
    exfalso.
    apply Hlast_even.
    destruct (odd_rem_iff_odd last ltac:(lia)) as [_ H].
    apply H; exact Hodd.
  - pose proof (last_digit_rem_bounds x ltac:(lia)).
    lia.
Qed.


Lemma proof_of_p146_specialFilter_safety_wit_15 : p146_specialFilter_safety_wit_15.
Proof.
  pre_process.
  match goal with
  | H : special_filter_prefix i input_l num |- _ =>
      pose proof (special_filter_prefix_count_bounds i input_l num H)
  end.
  entailer!.
Qed. 

Lemma proof_of_p146_specialFilter_entail_wit_1 : p146_specialFilter_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  apply special_filter_prefix_0.
Qed. 

Lemma proof_of_p146_specialFilter_entail_wit_2 : p146_specialFilter_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  - apply first_digit_state_init. lia.
  - pose proof (last_digit_rem_bounds (Znth i input_l 0) ltac:(lia)); lia.
  - pose proof (last_digit_rem_bounds (Znth i input_l 0) ltac:(lia)); lia.
Qed. 

Lemma proof_of_p146_specialFilter_entail_wit_3 : p146_specialFilter_entail_wit_3.
Proof.
  pre_process.
  entailer!.
  apply first_digit_state_step; try assumption; lia.
Qed. 

Lemma proof_of_p146_specialFilter_entail_wit_4 : p146_specialFilter_entail_wit_4.
Proof.
  pre_process.
  entailer!.
  pose proof H14 as Hstate.
  destruct Hstate as [fuel [[Hfirst_lo Hfirst_hi] [Hpow Hfd]]].
  apply special_number_intro_from_digits
    with (x := Znth i input_l 0) (first := first) (last := last);
    try assumption; lia.
Qed. 

Lemma proof_of_p146_specialFilter_entail_wit_5_1 : p146_specialFilter_entail_wit_5_1.
Proof.
  pre_process.
  entailer!.
  eapply special_filter_prefix_snoc_special; eauto; lia.
Qed. 

Lemma proof_of_p146_specialFilter_entail_wit_5_2 : p146_specialFilter_entail_wit_5_2.
Proof.
  pre_process.
  entailer!.
  match goal with
  | Hs : first_digit_state _ first |- _ =>
      pose proof Hs as Hstate;
      destruct Hstate as [fuel [[Hfirst_lo Hfirst_hi] [Hpow Hfd]]]
  end.
  eapply special_filter_prefix_snoc_not_special; eauto; try lia.
  eapply special_number_false_first_even; eauto; lia.
Qed. 

Lemma proof_of_p146_specialFilter_entail_wit_5_3 : p146_specialFilter_entail_wit_5_3.
Proof.
  pre_process.
  entailer!.
  match goal with
  | Hs : first_digit_state _ first |- _ =>
      pose proof Hs as Hstate;
      destruct Hstate as [fuel [[Hfirst_lo Hfirst_hi] [Hpow Hfd]]]
  end.
  eapply special_filter_prefix_snoc_not_special; eauto; try lia.
  eapply special_number_false_last_even; eauto; lia.
Qed. 

Lemma proof_of_p146_specialFilter_entail_wit_6_2 : p146_specialFilter_entail_wit_6_2.
Proof.
  pre_process.
  entailer!.
  eapply special_filter_prefix_snoc_not_special; eauto; try lia.
  apply special_number_false_of_le10; lia.
Qed. 

Lemma proof_of_p146_specialFilter_return_wit_1 : p146_specialFilter_return_wit_1.
Proof.
  pre_process.
  replace i with nums_size_pre by lia.
  match goal with
  | Hlen : nums_size_pre = Zlength input_l |- _ => rewrite Hlen in *
  end.
  replace i with (Zlength input_l) in * by lia.
  entailer!.
  apply problem_146_spec_of_prefix_full.
  assumption.
Qed. 

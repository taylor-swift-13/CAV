Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p108_count_nums Require Import p108_count_nums_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.

Import naive_C_Rules.
Require Import p108_count_nums.
Local Open Scope sac.
From AUXLib Require Import ListLib.

Local Open Scope list_scope.

(* Proof helpers moved from p108_count_nums.v so public contract files expose definitions only. *)

Lemma signed_digit_loop_last : forall fuel current sum,
  0 <= current < 10 ->
  signed_digit_loop fuel current sum = sum - current.
Proof.
  intros fuel.
  destruct fuel; intros; simpl; auto.
  assert ((current <? 10) = true) by (apply Z.ltb_lt; lia).
  rewrite H0; auto.
Qed.
Lemma sum_digits_nonpos_abs : forall x,
  x <= 0 ->
  sum_digits x = signed_digit_loop 11 (Z.abs x) 0.
Proof.
  intros.
  unfold sum_digits.
  destruct (x >? 0) eqn:Hgt.
  - apply Z.gtb_lt in Hgt. lia.
  - reflexivity.
Qed.
Lemma sublist_snoc_Znth_108 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0].
Proof.
  intros.
  rewrite (sublist_split 0 (i + 1) i l).
  replace (sublist i (i + 1) l) with (Znth i l 0 :: nil).
  reflexivity.
  - symmetry. apply sublist_single.
    lia.
  - lia.
  - lia.
Qed.
Lemma count_nums_impl_app_hit : forall xs x,
  sum_digits x > 0 ->
  count_nums_impl (xs ++ [x]) = count_nums_impl xs + 1.
Proof.
  intros.
  unfold count_nums_impl.
  rewrite filter_app.
  simpl.
  assert ((sum_digits x >? 0) = true) by (apply Z.gtb_lt; lia).
  rewrite H0.
  rewrite app_length.
  simpl.
  lia.
Qed.
Lemma count_nums_impl_app_miss : forall xs x,
  sum_digits x <= 0 ->
  count_nums_impl (xs ++ [x]) = count_nums_impl xs.
Proof.
  intros.
  unfold count_nums_impl.
  rewrite filter_app.
  simpl.
  destruct (sum_digits x >? 0) eqn:Hgt.
  - apply Z.gtb_lt in Hgt. lia.
  - rewrite app_length.
    simpl.
    lia.
Qed.
Lemma count_nums_impl_bounds : forall l,
  0 <= count_nums_impl l <= Zlength l.
Proof.
  intros.
  unfold count_nums_impl.
  rewrite Zlength_correct.
  split.
  - lia.
  - apply Nat2Z.inj_le.
    apply filter_length_le.
Qed.
Lemma count_nums_prefix_bounds : forall i l num,
  count_nums_prefix i l num ->
  0 <= num <= i.
Proof.
  intros i l num Hpref.
  unfold count_nums_prefix in Hpref.
  destruct Hpref as [Hbounds Hnum].
  subst num.
  pose proof (count_nums_impl_bounds (sublist 0 i l)) as Hcnt.
  rewrite Zlength_correct in Hcnt.
  rewrite sublist_length in Hcnt.
  lia.
  - lia.
  - destruct Hbounds as [_ Hle].
    exact Hle.
Qed.
Lemma count_nums_prefix_init : forall l,
  0 <= Zlength l ->
  count_nums_prefix 0 l 0.
Proof.
  intros.
  unfold count_nums_prefix.
  split.
  - lia.
  - unfold count_nums_impl, sublist.
    simpl.
    reflexivity.
Qed.
Lemma count_nums_prefix_hit : forall i l num,
  count_nums_prefix i l num ->
  0 <= i < Zlength l ->
  sum_digits (Znth i l 0) > 0 ->
  count_nums_prefix (i + 1) l (num + 1).
Proof.
  intros i l num Hpref Hi Hhit.
  unfold count_nums_prefix in *.
  destruct Hpref as [Hbounds Hnum].
  split.
  - lia.
  - rewrite sublist_snoc_Znth_108 by lia.
    rewrite count_nums_impl_app_hit by exact Hhit.
    lia.
Qed.
Lemma count_nums_prefix_miss : forall i l num,
  count_nums_prefix i l num ->
  0 <= i < Zlength l ->
  sum_digits (Znth i l 0) <= 0 ->
  count_nums_prefix (i + 1) l num.
Proof.
  intros i l num Hpref Hi Hmiss.
  unfold count_nums_prefix in *.
  destruct Hpref as [Hbounds Hnum].
  split.
  - lia.
  - rewrite sublist_snoc_Znth_108 by lia.
    rewrite count_nums_impl_app_miss by exact Hmiss.
    lia.
Qed.
Lemma digit_scan_state_init : forall x,
  0 <= x <= INT_MAX ->
  digit_scan_state x x 0.
Proof.
  intros.
  unfold digit_scan_state.
  split.
  - lia.
  - exists 11%nat.
    repeat split; try lia.
Qed.
Lemma digit_scan_state_step : forall original current sum,
  digit_scan_state original current sum ->
  current >= 10 ->
  digit_scan_state original (current / 10) (sum + current mod 10).
Proof.
  intros original current sum Hstate Hcur.
  unfold digit_scan_state in *.
  destruct Hstate as [Horig [fuel [Hcurrent [Hpow [Hsum [Hsum_cur Heq]]]]]].
  remember fuel as fuel_old eqn:Hfuel_old.
  destruct fuel_old as [ | fuel_tail ].
  {
    simpl in Hpow.
    lia.
  }
  simpl in Heq.
  assert ((current <? 10) = false) as Hltb by (apply Z.ltb_ge; lia).
  rewrite Hltb in Heq.
  assert (0 <= current mod 10 < 10) by (apply Z.mod_pos_bound; lia).
  assert (current mod 10 + current / 10 <= current).
  {
    assert (current = 10 * (current / 10) + current mod 10) by (apply Z.div_mod; lia).
    nia.
  }
  assert (Hdiv_bounds: 0 <= current / 10 <= original).
  {
    split.
    - apply Z.div_pos; lia.
    - assert (current / 10 <= current) by (apply Z.div_le_upper_bound; lia).
      lia.
  }
  split.
  - lia.
  - exists fuel_tail.
    split.
    + exact Hdiv_bounds.
    + split.
      * assert (Hcur_lt: current < 10 * 10 ^ Z.of_nat fuel_tail).
        {
          subst fuel.
          replace (10 ^ Z.of_nat (S fuel_tail)) with (10 * 10 ^ Z.of_nat fuel_tail) in Hpow.
          exact Hpow.
          rewrite Nat2Z.inj_succ.
          rewrite Z.pow_succ_r by lia.
          lia.
        }
        apply Z.div_lt_upper_bound.
        -- lia.
        -- nia.
      * split.
        -- lia.
        -- split.
          ++ nia.
          ++ exact Heq.
Qed.
Lemma digit_scan_state_final_hit : forall x current sum,
  x <= 0 ->
  current < 10 ->
  digit_scan_state (Z.abs x) current sum ->
  sum - current > 0 ->
  sum_digits x > 0.
Proof.
  intros x current sum Hx Hcur Hstate Hhit.
  unfold digit_scan_state in Hstate.
  destruct Hstate as [_ [fuel [[Hcur_nonneg _] [_ [_ [_ Heq]]]]]].
  rewrite sum_digits_nonpos_abs by lia.
  rewrite <- Heq.
  rewrite signed_digit_loop_last by lia.
  exact Hhit.
Qed.
Lemma digit_scan_state_final_miss : forall x current sum,
  x <= 0 ->
  current < 10 ->
  digit_scan_state (Z.abs x) current sum ->
  sum - current <= 0 ->
  sum_digits x <= 0.
Proof.
  intros x current sum Hx Hcur Hstate Hmiss.
  unfold digit_scan_state in Hstate.
  destruct Hstate as [_ [fuel [[Hcur_nonneg _] [_ [_ [_ Heq]]]]]].
  rewrite sum_digits_nonpos_abs by lia.
  rewrite <- Heq.
  rewrite signed_digit_loop_last by lia.
  exact Hmiss.
Qed.
Lemma problem_108_spec_of_prefix : forall l out,
  count_nums_prefix (Zlength l) l out ->
  problem_108_spec l out.
Proof.
  intros l out Hpref.
  unfold count_nums_prefix, problem_108_spec in *.
  destruct Hpref as [_ Hout].
  rewrite sublist_self in Hout by lia.
  exact Hout.
Qed.


Lemma proof_of_abs_return_wit_1 : abs_return_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_abs_return_wit_2 : abs_return_wit_2.
Proof.
  pre_process.
Qed.

Lemma proof_of_p108_count_nums_safety_wit_4 : p108_count_nums_safety_wit_4.
Proof.
  pre_process.
  pose proof (count_nums_prefix_bounds i input_l num H8).
  entailer!.
Qed.

Lemma proof_of_p108_count_nums_safety_wit_8 : p108_count_nums_safety_wit_8.
Proof.
  pre_process.
  unfold digit_scan_state in H9.
  destruct H9 as [_ [fuel [[_ Hw_upper] [_ [Hsum [Hsum_cur _]]]]]].
  assert (w % 10 = w mod 10) as Hrem.
  { apply Z.rem_mod_nonneg; lia. }
  assert (0 <= w mod 10 < 10) by (apply Z.mod_pos_bound; lia).
  rewrite Hrem.
  entailer!.
Qed.

Lemma proof_of_p108_count_nums_safety_wit_13 : p108_count_nums_safety_wit_13.
Proof.
  pre_process.
  unfold digit_scan_state in H9.
  destruct H9 as [_ [fuel [[Hw_nonneg Hw_upper] [_ [Hsum [Hsum_cur _]]]]]].
  entailer!.
Qed.

Lemma proof_of_p108_count_nums_safety_wit_15 : p108_count_nums_safety_wit_15.
Proof.
  pre_process.
  pose proof (count_nums_prefix_bounds i input_l num H8).
  entailer!.
Qed.

Lemma proof_of_p108_count_nums_entail_wit_1 : p108_count_nums_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  apply count_nums_prefix_init.
  rewrite <- H1.
  lia.
Qed.

Lemma proof_of_p108_count_nums_entail_wit_2 : p108_count_nums_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  subst retval.
  apply digit_scan_state_init.
  assert (INT_MIN < Znth i input_l 0 <= INT_MAX).
  {
    match goal with
    | Hrange: count_nums_int_range input_l |- _ =>
        apply Hrange; lia
    end.
  }
  rewrite Z.abs_neq by lia.
  lia.
Qed.

Lemma proof_of_p108_count_nums_entail_wit_3 : p108_count_nums_entail_wit_3.
Proof.
  pre_process.
  assert (0 <= w) as Hw_nonneg.
  {
    unfold digit_scan_state in H9.
    destruct H9 as [_ [fuel [[Hw_nonneg _] _]]].
    exact Hw_nonneg.
  }
  assert (w ÷ 10 = w / 10) as Hquot.
  { apply Z.quot_div_nonneg; lia. }
  assert (w % 10 = w mod 10) as Hrem.
  { apply Z.rem_mod_nonneg; lia. }
  rewrite Hquot, Hrem.
  entailer!.
  apply digit_scan_state_step; auto.
Qed.

Lemma proof_of_p108_count_nums_entail_wit_4_1 : p108_count_nums_entail_wit_4_1.
Proof.
  pre_process.
  entailer!.
  apply count_nums_prefix_hit; auto; try lia.
  unfold sum_digits.
  assert ((Znth i input_l 0 >? 0) = true) as Hgt by (apply Z.gtb_lt; lia).
  rewrite Hgt.
  lia.
Qed.

Lemma proof_of_p108_count_nums_entail_wit_4_2 : p108_count_nums_entail_wit_4_2.
Proof.
  pre_process.
  entailer!.
  apply count_nums_prefix_hit; auto; try lia.
  eapply digit_scan_state_final_hit; eauto; lia.
Qed.

Lemma proof_of_p108_count_nums_entail_wit_4_3 : p108_count_nums_entail_wit_4_3.
Proof.
  pre_process.
  entailer!.
  apply count_nums_prefix_miss; auto; try lia.
  eapply digit_scan_state_final_miss; eauto; lia.
Qed.

Lemma proof_of_p108_count_nums_return_wit_1 : p108_count_nums_return_wit_1.
Proof.
  pre_process.
  entailer!.
  apply problem_108_spec_of_prefix.
  replace (Zlength input_l) with i by lia.
  exact H7.
Qed.

Lemma proof_of_p108_count_nums_partial_solve_wit_3_pure : p108_count_nums_partial_solve_wit_3_pure.
Proof.
  pre_process.
  entailer!.
  match goal with
  | Hrange: count_nums_int_range input_l |- _ =>
      pose proof (Hrange i ltac:(lia)); lia
  end.
Qed.

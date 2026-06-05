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
From SimpleC.EE.CAV.verify_20260605_162851v_armstrong_number Require Import armstrong_number_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import armstrong_number.
Require Import armstrong_number_helper.
Local Open Scope sac.

Fixpoint pow10_nat (fuel : nat) : Z :=
  match fuel with
  | O => 1
  | S k => 10 * pow10_nat k
  end.

Lemma quot_div_10 : forall n, 0 <= n -> n ÷ 10 = n / 10.
Proof.
  intros n Hn.
  apply Z.quot_div_nonneg; lia.
Qed.

Lemma rem_mod_10 : forall n, 0 <= n -> n mod 10 = n % 10.
Proof.
  intros n Hn.
  symmetry.
  apply Z.rem_mod_nonneg; lia.
Qed.

Lemma quot_10_nonneg : forall n, 0 <= n -> 0 <= n ÷ 10.
Proof.
  intros n Hn.
  rewrite quot_div_10 by lia.
  apply Z.div_pos; lia.
Qed.

Lemma quot_10_lt_pos : forall n, 0 < n -> n ÷ 10 < n.
Proof.
  intros n Hn.
  rewrite quot_div_10 by lia.
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma rem_10_bounds : forall n, 0 <= n -> 0 <= n % 10 <= 9.
Proof.
  intros n Hn.
  rewrite <- rem_mod_10 by lia.
  pose proof (Z.mod_pos_bound n 10) as Hmod.
  lia.
Qed.

Lemma zpow_nat_z_0 : forall d, zpow_nat_z d 0 = 1.
Proof.
  intros d.
  unfold zpow_nat_z.
  reflexivity.
Qed.

Lemma zpow_nat_z_succ : forall d i, 0 <= i -> zpow_nat_z d (i + 1) = d * zpow_nat_z d i.
Proof.
  intros d i Hi.
  unfold zpow_nat_z.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  reflexivity.
Qed.

Lemma zpow_nat_z_bound : forall d i,
  0 <= d <= 9 ->
  0 <= i <= 8 ->
  0 <= zpow_nat_z d i <= 43046721.
Proof.
  intros d i Hd Hi.
  assert (Hd_cases :
    d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9) by lia.
  assert (Hi_cases :
    i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) by lia.
  destruct Hi_cases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  destruct Hd_cases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
    unfold zpow_nat_z; vm_compute; tauto.
Qed.

Lemma count_digits_bounded_stable :
  forall fuel n,
    fuel <> O ->
    0 <= n < pow10_nat fuel ->
    count_digits_bounded n fuel = count_digits_bounded n (S fuel).
Proof.
  induction fuel as [|fuel IH]; intros n Hfuel Hrange; [contradiction|].
  destruct fuel as [|fuel].
  - simpl in Hrange.
    destruct (n <? 10) eqn:Hltb.
    + unfold count_digits_bounded.
      rewrite Hltb.
      reflexivity.
    + apply Z.ltb_ge in Hltb.
      lia.
  - destruct (n <? 10) eqn:Hltb.
    + unfold count_digits_bounded.
      rewrite Hltb.
      reflexivity.
    + apply Z.ltb_ge in Hltb as Hge.
      simpl in Hrange.
      unfold count_digits_bounded at 1 2.
      rewrite Hltb.
      simpl.
      change (1 + count_digits_bounded (n / 10) (S fuel) =
              1 + count_digits_bounded (n / 10) (S (S fuel))).
      f_equal.
      apply IH.
      * discriminate.
      * split.
        -- apply Z.div_pos; lia.
        -- apply Z.div_lt_upper_bound.
           ++ lia.
           ++ replace (pow10_nat (S fuel) * 10) with (10 * pow10_nat (S fuel)) by nia.
              destruct Hrange as [_ Hupper].
              exact Hupper.
Qed.

Lemma count_digits_bounded_7_8 :
  forall n,
    0 <= n <= 9999999 ->
    count_digits_bounded n 7 = count_digits_bounded n 8.
Proof.
  intros n Hn.
  apply count_digits_bounded_stable; [discriminate|].
  simpl.
  split; lia.
Qed.

Lemma count_digits_bounded_positive :
  forall fuel n,
    fuel <> O ->
    0 <= n ->
    1 <= count_digits_bounded n fuel.
Proof.
  induction fuel as [|fuel IH]; intros n Hfuel Hn; [contradiction|].
  destruct (n <? 10) eqn:Hltb.
  - unfold count_digits_bounded.
    rewrite Hltb.
    lia.
  - apply Z.ltb_ge in Hltb as Hge.
    destruct fuel as [|fuel].
    + unfold count_digits_bounded.
      rewrite Hltb.
      simpl.
      lia.
    + unfold count_digits_bounded at 1.
      rewrite Hltb.
      change (1 <= 1 + count_digits_bounded (n / 10) (S fuel)).
      assert (Hq : 0 <= n / 10) by (apply Z.div_pos; lia).
      pose proof (IH (n / 10) ltac:(discriminate) Hq) as Hpos.
      lia.
Qed.

Lemma count_digits_z_positive : forall n, 0 <= n -> 1 <= count_digits_z n.
Proof.
  intros n Hn.
  unfold count_digits_z.
  destruct (Z.eqb_spec n 0).
  - lia.
  - apply count_digits_bounded_positive; lia.
Qed.

Lemma count_digits_z_lt_10 : forall n, 0 <= n < 10 -> count_digits_z n = 1.
Proof.
  intros n Hn.
  unfold count_digits_z.
  destruct (Z.eqb_spec n 0) as [-> | Hneq].
  - reflexivity.
  - unfold count_digits_bounded.
    destruct (n <? 10) eqn:Hltb.
    + reflexivity.
    + apply Z.ltb_ge in Hltb.
      lia.
Qed.

Lemma count_digits_z_step : forall n,
  10 <= n <= 99999999 ->
  count_digits_z n = 1 + count_digits_z (n / 10).
Proof.
  intros n Hn.
  unfold count_digits_z.
  assert (Hq : 0 < n / 10 <= 9999999).
  {
    split.
    - apply Z.div_str_pos; lia.
    - assert (Hlt : n / 10 < 10000000).
      { apply Z.div_lt_upper_bound; lia. }
      lia.
  }
  destruct (Z.eqb_spec n 0) as [Hz | Hnz].
  { lia. }
  unfold count_digits_bounded at 1.
  destruct (n <? 10) eqn:Hltb.
  - apply Z.ltb_lt in Hltb. lia.
  - destruct (Z.eqb_spec (n / 10) 0) as [Hq0 | Hq0].
    + lia.
    + change (1 + count_digits_bounded (n / 10) 7 =
              1 + count_digits_bounded (n / 10) 8).
      rewrite <- (count_digits_bounded_7_8 (n / 10)).
      * reflexivity.
      * split; lia.
Qed.

Lemma armstrong_sum_aux_stable :
  forall fuel n d,
    fuel <> O ->
    0 <= n < pow10_nat fuel ->
    armstrong_sum_aux n d fuel = armstrong_sum_aux n d (S fuel).
Proof.
  induction fuel as [|fuel IH]; intros n d Hfuel Hrange; [contradiction|].
  destruct (Z.eqb_spec n 0) as [-> | Hneq].
  - reflexivity.
  - destruct fuel as [|fuel].
    + simpl in Hrange.
      unfold armstrong_sum_aux at 1 2.
      assert (Hdiv0 : n / 10 = 0) by (apply Z.div_small; lia).
      destruct (n =? 0) eqn:Hz.
      * apply Z.eqb_eq in Hz. contradiction.
      * rewrite Hdiv0. reflexivity.
    + unfold armstrong_sum_aux at 1 2.
      destruct (n =? 0) eqn:Hz.
      * apply Z.eqb_eq in Hz. contradiction.
      * f_equal.
        apply IH.
        -- discriminate.
        -- split.
           ++ apply Z.div_pos; lia.
           ++ apply Z.div_lt_upper_bound.
              ** lia.
              ** replace (pow10_nat (S fuel) * 10) with (10 * pow10_nat (S fuel)) by nia.
                 destruct Hrange as [_ Hupper].
                 exact Hupper.
Qed.

Lemma armstrong_sum_aux_7_8 :
  forall n d,
    0 <= n <= 9999999 ->
    armstrong_sum_aux n d 7 = armstrong_sum_aux n d 8.
Proof.
  intros n d Hn.
  apply armstrong_sum_aux_stable; [discriminate|].
  simpl.
  split; lia.
Qed.

Lemma armstrong_sum_z_zero : forall d, armstrong_sum_z 0 d = 0.
Proof.
  intros d.
  unfold armstrong_sum_z.
  reflexivity.
Qed.

Lemma armstrong_sum_z_step : forall n d,
  0 < n ->
  1 <= d <= 8 ->
  armstrong_sum_z n d = zpow_nat_z (n mod 10) d + armstrong_sum_aux (n / 10) d 7.
Proof.
  intros n d Hn Hd.
  unfold armstrong_sum_z at 1.
  simpl.
  assert (Hz : (n =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Hz.
  change (zpow_nat (n mod 10) (Z.to_nat d) + armstrong_sum_aux (n / 10) d 7 =
          zpow_nat_z (n mod 10) d + armstrong_sum_aux (n / 10) d 7).
  unfold zpow_nat_z.
  reflexivity.
Qed.

Lemma armstrong_sum_z_unroll : forall n d,
  0 < n <= 99999999 ->
  1 <= d <= 8 ->
  armstrong_sum_z n d = zpow_nat_z (n mod 10) d + armstrong_sum_z (n / 10) d.
Proof.
  intros n d Hn Hd.
  pose proof (armstrong_sum_z_step n d ltac:(lia) Hd) as Hstep.
  rewrite Hstep.
  destruct (Z.eq_dec (n / 10) 0) as [Hq0 | Hq0].
  - rewrite Hq0.
    unfold armstrong_sum_z.
    simpl.
    reflexivity.
  - change (zpow_nat_z (n mod 10) d + armstrong_sum_aux (n / 10) d 7 =
            zpow_nat_z (n mod 10) d + armstrong_sum_aux (n / 10) d 8).
    rewrite <- (armstrong_sum_aux_7_8 (n / 10) d).
    + reflexivity.
    + split.
      * apply Z.div_pos; lia.
      * assert (Hlt : n / 10 < 10000000).
        { apply Z.div_lt_upper_bound; lia. }
        lia.
Qed.

Lemma armstrong_sum_aux_bound :
  forall fuel n d,
    0 <= n ->
    1 <= d <= 8 ->
    0 <= armstrong_sum_aux n d fuel <= Z.of_nat fuel * 43046721.
Proof.
  induction fuel as [|fuel IH]; intros n d Hn Hd.
  - simpl. lia.
  - simpl.
    destruct (Z.eqb_spec n 0).
    + lia.
    + pose proof (rem_10_bounds n Hn) as Hrem.
      pose proof (zpow_nat_z_bound (n % 10) d) as Hp.
      assert (Hpow : 0 <= zpow_nat_z (n % 10) d <= 43046721).
      {
        apply Hp; lia.
      }
      pose proof (IH (n / 10) d) as Hrest.
      assert (Hq : 0 <= n / 10) by (apply Z.div_pos; lia).
      specialize (Hrest Hq Hd).
      replace (Z.of_nat (S fuel) * 43046721) with (43046721 + Z.of_nat fuel * 43046721) by lia.
      destruct Hpow as [Hpow_lo Hpow_hi].
      destruct Hrest as [Hrest_lo Hrest_hi].
      unfold zpow_nat_z in Hpow_lo, Hpow_hi.
      rewrite <- rem_mod_10 in Hpow_lo, Hpow_hi by lia.
      split.
      * apply Z.add_nonneg_nonneg.
        -- exact Hpow_lo.
        -- exact Hrest_lo.
      * eapply Z.le_trans.
        -- apply Z.add_le_mono; eauto.
        -- lia.
Qed.

Lemma armstrong_sum_z_bound : forall n d,
  0 <= n ->
  1 <= d <= 8 ->
  0 <= armstrong_sum_z n d <= 344373768.
Proof.
  intros n d Hn Hd.
  unfold armstrong_sum_z.
  pose proof (armstrong_sum_aux_bound 8 n d Hn Hd) as H.
  replace (Z.of_nat 8 * 43046721) with 344373768 in H by reflexivity.
  exact H.
Qed.

Lemma proof_of_armstrong_number_safety_wit_16 : armstrong_number_safety_wit_16.
Proof.
  pre_process.
  subst p.
  replace (zpow_nat_z d i * d) with (d * zpow_nat_z d i) by lia.
  rewrite <- zpow_nat_z_succ by lia.
  pose proof (zpow_nat_z_bound d (i + 1)) as Hp.
  assert (0 <= i + 1 <= 8) as Hi1 by lia.
  specialize (Hp ltac:(lia) Hi1).
  destruct Hp as [Hp_lo Hp_hi].
  split.
  - eapply Z.le_trans.
    + exact Hp_hi.
    + lia.
  - eapply Z.le_trans with (m := 0).
    + lia.
    + exact Hp_lo.
Qed.

Lemma proof_of_armstrong_number_safety_wit_18 : armstrong_number_safety_wit_18.
Proof.
  pre_process.
  assert (Hdigits : 1 <= digits <= 8) by lia.
  assert (Hdigits_nonneg : 0 <= digits <= 8) by lia.
  pose proof (armstrong_sum_z_bound n_pre digits ltac:(lia) Hdigits) as Htotal.
  pose proof (armstrong_sum_z_bound temp digits ltac:(lia) Hdigits) as Htail.
  pose proof (zpow_nat_z_bound d digits ltac:(lia) Hdigits_nonneg) as Hpbound.
  destruct Htotal as [_ Htotal_hi].
  destruct Htail as [Htail_lo _].
  destruct Hpbound as [Hp_lo Hp_hi].
  subst p.
  split.
  - assert (Hsum_hi : sum <= 344373768) by lia.
    assert (Hsp_hi : sum + zpow_nat_z d digits <= 344373768 + 43046721) by lia.
    eapply Z.le_trans.
    + exact Hsp_hi.
    + lia.
  - eapply Z.le_trans with (m := 0).
    + lia.
    + apply Z.add_nonneg_nonneg; lia.
Qed.

Lemma proof_of_armstrong_number_entail_wit_1_1 : armstrong_number_entail_wit_1_1.
Proof.
  pre_process.
  Left.
  entailer!.
  assert (Hpos : 0 < n_pre) by lia.
  pose proof (count_digits_z_positive n_pre ltac:(lia)) as Hdigits_pos.
  repeat split; lia.
Qed.


Lemma count_digits_bounded_le_fuel : forall fuel n, count_digits_bounded n fuel <= Z.of_nat fuel.
Proof.
  induction fuel as [|fuel IH]; intros n.
  - simpl. lia.
  - cbn [count_digits_bounded]. rewrite Nat2Z.inj_succ.
    destruct (n <? 10) eqn:E.
    + lia.
    + specialize (IH (n / 10)). lia.
Qed.

Lemma count_digits_z_le_8 : forall n, count_digits_z n <= 8.
Proof.
  intros n. unfold count_digits_z. destruct (Z.eqb n 0).
  - lia.
  - pose proof (count_digits_bounded_le_fuel 8 n) as H.
    change (Z.of_nat 8) with 8 in H. lia.
Qed.

Lemma proof_of_armstrong_number_entail_wit_2 : armstrong_number_entail_wit_2.
Proof.
  pre_process. Left. entailer!.
  - intro Hn.
    match goal with Hh : 0 < n_pre -> _ |- _ =>
      destruct (Hh Hn) as [[[Hpos_np Hpos_sum] Heq0] Hstep] end.
    assert (Htp : temp > 0) by lia.
    pose proof (Hstep Htp) as Hrel.
    assert (Hqnn : 0 <= temp / 10) by (apply Z.div_pos; lia).
    rewrite (quot_div_10 temp ltac:(lia)).
    split; [split|].
    + split.
      * exact Hpos_np.
      * pose proof (count_digits_z_positive (temp / 10) Hqnn). lia.
    + intro Hq0.
      assert (Hlt : temp < 10).
      { destruct (Z_lt_ge_dec temp 10) as [Hl|Hg]; [exact Hl|].
        assert (0 < temp / 10) by (apply Z.div_str_pos; lia). lia. }
      pose proof (count_digits_z_lt_10 temp ltac:(lia)) as Hc1. lia.
    + intro Hqpos.
      assert (Hge10 : 10 <= temp).
      { destruct (Z_lt_ge_dec temp 10) as [Hl|Hg]; [|lia].
        assert (temp / 10 = 0) by (apply Z.div_small; lia). lia. }
      assert (Htmax : temp <= 99999999) by lia.
      pose proof (count_digits_z_step temp (conj Hge10 Htmax)) as Hs. lia.
  - assert (Hn : 0 < n_pre) by lia.
    match goal with Hh : 0 < n_pre -> _ |- _ =>
      destruct (Hh Hn) as [_ Hstep] end.
    assert (Htp : temp > 0) by lia.
    pose proof (Hstep Htp) as Hrel.
    pose proof (count_digits_z_le_8 n_pre).
    pose proof (count_digits_z_positive temp ltac:(lia)). lia.
  - rewrite (quot_div_10 temp ltac:(lia)).
    apply Z.div_le_upper_bound; nia.
  - apply quot_10_nonneg; lia.
Qed.
Lemma proof_of_armstrong_number_entail_wit_3_1 : armstrong_number_entail_wit_3_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_armstrong_number_entail_wit_3_2 : armstrong_number_entail_wit_3_2.
Proof.
  pre_process.
  assert (Hn0 : n_pre = 0) by lia.
  match goal with
  | H : (n_pre = 0 -> (temp = 0 /\ digits = 1)) |- _ =>
      pose proof (H Hn0) as Hzero
  end.
  destruct Hzero as [Htemp Hdigits].
  subst n_pre temp digits.
  entailer!.
Qed.

Lemma proof_of_armstrong_number_entail_wit_4 : armstrong_number_entail_wit_4.
Proof.
  pre_process.
Qed.

Lemma proof_of_armstrong_number_entail_wit_5 : armstrong_number_entail_wit_5.
Proof.
  pre_process.
  entailer!.
  intros Hzero.
  subst sum.
  rewrite Hzero in H5 |- *.
  rewrite armstrong_sum_z_zero in H5 |- *.
  lia.
Qed.

Lemma proof_of_armstrong_number_entail_wit_6 : armstrong_number_entail_wit_6.
Proof.
  pre_process.
  pose proof (rem_10_bounds temp ltac:(lia)) as Hrem.
  entailer!.
Qed.
Lemma proof_of_armstrong_number_entail_wit_7 : armstrong_number_entail_wit_7.
Proof.
  pre_process.
Qed.
Lemma proof_of_armstrong_number_entail_wit_8 : armstrong_number_entail_wit_8.
Proof.
  pre_process. entailer!.
  rewrite zpow_nat_z_succ by lia.
  match goal with H : p_2 = zpow_nat_z d_2 i |- _ => rewrite H end.
  ring.
Qed.
Lemma proof_of_armstrong_number_entail_wit_9 : armstrong_number_entail_wit_9.
Proof.
  pre_process.
  assert (i = digits) by lia.
  subst i.
  entailer!.
Qed.

Lemma proof_of_armstrong_number_entail_wit_10 : armstrong_number_entail_wit_10.
Proof.
  pre_process. Exists 0 digits_2. entailer!.
  - intro Hqgt.
    subst d p.
    assert (Hstep : armstrong_sum_z temp digits_2 =
        zpow_nat_z (temp mod 10) digits_2 + armstrong_sum_z (temp / 10) digits_2)
      by (apply armstrong_sum_z_unroll; lia).
    rewrite quot_div_10 by lia.
    rewrite rem_mod_10 in Hstep by lia.
    lia.
  - intro Hq0.
    subst d p.
    assert (Hstep : armstrong_sum_z temp digits_2 =
        zpow_nat_z (temp mod 10) digits_2 + armstrong_sum_z (temp / 10) digits_2)
      by (apply armstrong_sum_z_unroll; lia).
    rewrite quot_div_10 in Hq0 by lia.
    rewrite Hq0 in Hstep.
    rewrite armstrong_sum_z_zero in Hstep.
    rewrite rem_mod_10 in Hstep by lia.
    lia.
  - rewrite (quot_div_10 temp ltac:(lia)).
    apply Z.div_le_upper_bound; nia.
  - apply quot_10_nonneg; lia.
Qed.
Lemma proof_of_armstrong_number_return_wit_1 : armstrong_number_return_wit_1.
Proof.
  pre_process.
  subst digits.
  unfold is_armstrong_z.
  rewrite <- H4.
  rewrite <- H.
  rewrite Z.eqb_refl.
  entailer!.
Qed.

Lemma proof_of_armstrong_number_return_wit_2 : armstrong_number_return_wit_2.
Proof.
  pre_process.
  subst digits.
  unfold is_armstrong_z.
  rewrite <- H4.
  apply Z.eqb_neq in H.
  rewrite H.
  entailer!.
Qed.

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
From SimpleC.EE.CAV.ground_truth_p094_skjkasdkd Require Import p094_skjkasdkd_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.Znumtheory.

Import naive_C_Rules.
Require Import p094_skjkasdkd.
Local Open Scope sac.
From AUXLib Require Import ListLib.

Local Open Scope list_scope.

(* Proof helpers moved from p094_skjkasdkd.v so public contract files expose definitions only. *)

Lemma prime_gt_1_94 : forall p,
  prime p -> 1 < p.
Proof.
  intros p Hprime.
  inversion Hprime.
  assumption.
Qed.
Lemma largest_prime_prefix_init : forall lst,
  0 <= Zlength lst ->
  largest_prime_prefix 0 lst 0.
Proof.
  intros lst Hlen.
  unfold largest_prime_prefix.
  repeat split; try lia.
  left.
  split.
  - reflexivity.
  - intros k Hk. lia.
Qed.
Lemma largest_prime_prefix_skip_not_prime : forall i lst largest,
  largest_prime_prefix i lst largest ->
  0 <= i < Zlength lst ->
  ~ prime (Znth i lst 0) ->
  largest_prime_prefix (i + 1) lst largest.
Proof.
  intros i lst largest Hpref Hi Hnot.
  unfold largest_prime_prefix in *.
  destruct Hpref as [Hi_bounds [Hlargest Hseen]].
  repeat split; try lia.
  destruct Hseen as [[Hzero Hnone] | [Hprime [Hin Hmax]]].
  - left.
    split.
    + exact Hzero.
    + intros k Hk.
      destruct (Z.eq_dec k i) as [-> | Hneq].
      * exact Hnot.
      * apply Hnone. lia.
  - right.
    split.
    + exact Hprime.
    + split.
      * destruct Hin as [k [Hk Hval]].
        exists k. split; [lia | exact Hval].
      * intros k Hk Hpk.
        destruct (Z.eq_dec k i) as [-> | Hneq].
        -- contradiction.
        -- apply Hmax; try assumption; lia.
Qed.
Lemma largest_prime_prefix_skip_le : forall i lst largest,
  largest_prime_prefix i lst largest ->
  0 <= i < Zlength lst ->
  Znth i lst 0 <= largest ->
  largest_prime_prefix (i + 1) lst largest.
Proof.
  intros i lst largest Hpref Hi Hle.
  unfold largest_prime_prefix in *.
  destruct Hpref as [Hi_bounds [Hlargest Hseen]].
  repeat split; try lia.
  destruct Hseen as [[Hzero Hnone] | [Hprime [Hin Hmax]]].
  - left.
    split.
    + exact Hzero.
    + intros k Hk Hpk.
      destruct (Z.eq_dec k i) as [-> | Hneq].
      * pose proof (prime_gt_1_94 _ Hpk). lia.
      * apply (Hnone k); try assumption; lia.
  - right.
    split.
    + exact Hprime.
    + split.
      * destruct Hin as [k [Hk Hval]].
        exists k. split; [lia | exact Hval].
      * intros k Hk Hpk.
        destruct (Z.eq_dec k i) as [-> | Hneq].
        -- exact Hle.
        -- apply Hmax; try assumption; lia.
Qed.
Lemma largest_prime_prefix_update : forall i lst largest x,
  largest_prime_prefix i lst largest ->
  0 <= i < Zlength lst ->
  x = Znth i lst 0 ->
  0 <= x <= INT_MAX ->
  prime x ->
  largest < x ->
  largest_prime_prefix (i + 1) lst x.
Proof.
  intros i lst largest x Hpref Hi Hx Hrange Hprime Hgt.
  unfold largest_prime_prefix in *.
  destruct Hpref as [Hi_bounds [Hlargest Hseen]].
  repeat split; try lia.
  right.
  split.
  - exact Hprime.
  - split.
    + exists i. split; [lia | exact Hx].
    + intros k Hk Hpk.
      destruct (Z.eq_dec k i) as [-> | Hneq].
      * rewrite <- Hx. lia.
      * destruct Hseen as [[Hzero Hnone] | [Hprime_old [Hin Hmax]]].
        -- exfalso. apply (Hnone k); try assumption; lia.
        -- assert (Znth k lst 0 <= largest) by (apply Hmax; try assumption; lia).
           lia.
Qed.
Lemma prime_scan_state_init : forall x,
  1 < x <= INT_MAX ->
  prime_scan_state x 2 1.
Proof.
  intros.
  unfold prime_scan_state.
  repeat split; try lia;
    try (intros _ d Hd; lia);
    try (intros Hzero; lia).
Qed.
Lemma prime_scan_state_step_keep : forall x j flag,
  prime_scan_state x j flag ->
  j <= x / j ->
  x mod j <> 0 ->
  prime_scan_state x (j + 1) flag.
Proof.
  intros x j flag Hstate Hcond Hmod.
  unfold prime_scan_state in *.
  destruct Hstate as [Hx [Hj [Hflag [Hnonzero Hzero]]]].
  assert (x / j <= x) by (apply Z.div_le_upper_bound; nia).
  split.
  - lia.
  - split.
    + lia.
    + split.
      * lia.
      * split.
        -- intros Hnz d Hd.
           destruct (Z.eq_dec d j) as [-> | Hneq].
           ++ exact Hmod.
           ++ apply Hnonzero; try assumption; lia.
        -- intros Hz.
           destruct (Hzero Hz) as [d [Hd [Hd_lt Hdiv]]].
           exists d. split; [lia | split; [exact Hd_lt | exact Hdiv]].
Qed.
Lemma prime_scan_state_step_zero : forall x j flag,
  prime_scan_state x j flag ->
  j <= x / j ->
  x mod j = 0 ->
  prime_scan_state x (j + 1) 0.
Proof.
  intros x j flag Hstate Hcond Hmod.
  unfold prime_scan_state in *.
  destruct Hstate as [Hx [Hj [_ _]]].
  assert (x / j <= x) by (apply Z.div_le_upper_bound; nia).
  split.
  - lia.
  - split.
    + lia.
    + split.
      * lia.
      * split.
        -- intros Hnz. lia.
        -- intros _.
           exists j.
           split.
           ++ lia.
           ++ split.
              ** assert (j * j <= x).
                 {
                   assert (j * j <= j * (x / j)).
                   { apply Z.mul_le_mono_nonneg_l; lia. }
                   pose proof (Z.mul_div_le x j ltac:(lia)).
                   nia.
                 }
                 nia.
              ** exact Hmod.
Qed.
Lemma divide_trans_94 : forall a b c,
  (a | b) -> (b | c) -> (a | c).
Proof.
  intros a b c [x Hx] [y Hy].
  exists (y * x).
  rewrite Hy, Hx.
  ring.
Qed.
Lemma exists_prime_divisor_94 : forall n,
  1 < n ->
  exists p, prime p /\ (p | n) /\ 2 <= p <= n.
Proof.
  apply (well_founded_induction
           (Z.lt_wf 0)
           (fun n => 1 < n -> exists p, prime p /\ (p | n) /\ 2 <= p <= n)).
  intros n IH Hn.
  destruct (prime_dec n) as [Hprime | Hnot].
  - exists n.
    split.
    + exact Hprime.
    + split.
      * exists 1. lia.
      * lia.
  - destruct (not_prime_divide n Hn Hnot) as [d [[Hd_gt Hd_lt] Hdiv]].
    assert (Hrec : 0 <= d < n) by lia.
    destruct (IH d Hrec ltac:(lia)) as [p [Hp [Hpdiv Hrange]]].
    exists p.
    split.
    + exact Hp.
    + split.
      * eapply divide_trans_94; eauto.
      * lia.
Qed.
Lemma composite_small_prime_divisor_94 : forall n,
  1 < n ->
  ~ prime n ->
  exists p, prime p /\ (p | n) /\ 2 <= p < n /\ p <= n / p.
Proof.
  intros n Hn Hnot.
  destruct (not_prime_divide n Hn Hnot) as [d [[Hd_gt Hd_lt] Hdiv]].
  destruct Hdiv as [q Hn_eq].
  assert (Hd_pos : 0 < d) by lia.
  assert (Hq_gt1 : 1 < q).
  {
    destruct (Z_le_gt_dec q 1) as [Hq_le | Hq_gt].
    - assert (q <= 0 \/ q = 1) as Hq_case by lia.
      destruct Hq_case as [Hqle | Hqeq].
      + nia.
      + subst q. nia.
    - lia.
  }
  assert (Hq_pos : 0 < q) by lia.
  assert (Hd_case : d <= q \/ q < d) by lia.
  destruct Hd_case as [Hd_le_q | Hq_lt_d].
  - destruct (exists_prime_divisor_94 d ltac:(lia)) as [p [Hp [Hpdiv [Hp_ge Hp_le]]]].
    exists p.
    split.
    + exact Hp.
    + split.
      * eapply divide_trans_94; eauto. exists q. exact Hn_eq.
      * split.
        -- lia.
        -- assert (p <= d) by lia.
           assert (d <= n / d).
           {
             apply Z.div_le_lower_bound; nia.
           }
           assert (n / d <= n / p).
           {
             apply Z.div_le_lower_bound; try lia.
             pose proof (Z.mul_div_le n d ltac:(lia)).
             nia.
           }
           lia.
  - destruct (exists_prime_divisor_94 q ltac:(lia)) as [p [Hp [Hpdiv [Hp_ge Hp_le]]]].
    exists p.
    split.
    + exact Hp.
    + split.
      * destruct Hpdiv as [m Hq_eq].
        exists (d * m).
        rewrite Hn_eq, Hq_eq.
        ring.
      * split.
        -- lia.
        -- assert (p <= q) by lia.
           assert (q <= n / q).
           {
             rewrite Hn_eq.
             apply Z.div_le_lower_bound; nia.
           }
           assert (n / q <= n / p).
           {
             apply Z.div_le_lower_bound; try lia.
             pose proof (Z.mul_div_le n q ltac:(lia)).
             nia.
           }
           lia.
Qed.
Lemma prime_scan_state_zero_not_prime : forall x j,
  prime_scan_state x j 0 ->
  ~ prime x.
Proof.
  intros x j Hstate Hprime.
  unfold prime_scan_state in Hstate.
  destruct Hstate as [_ [_ [_ [_ Hzero]]]].
  destruct (Hzero eq_refl) as [d [Hd [Hd_lt Hmod]]].
  assert (Hdiv : (d | x)).
  { apply Z.mod_divide; lia. }
  pose proof (prime_divisors x Hprime d Hdiv) as [Heq | [Heq | [Heq | Heq]]]; lia.
Qed.
Lemma prime_scan_state_exit_prime : forall x j flag,
  prime_scan_state x j flag ->
  flag <> 0 ->
  j > x / j ->
  prime x.
Proof.
  intros x j flag Hstate Hflag Hexit.
  destruct (prime_dec x) as [Hprime | Hnot].
  - exact Hprime.
  - unfold prime_scan_state in Hstate.
    destruct Hstate as [Hx [Hj [_ [Hnodiv _]]]].
    destruct (composite_small_prime_divisor_94 x ltac:(lia) Hnot)
      as [p [Hp [Hdiv [[Hp_ge Hp_lt] Hp_le_div]]]].
    assert (Hp_lt_j : p < j).
    {
      destruct (Z_lt_ge_dec p j) as [Hlt | Hge].
      - exact Hlt.
      - exfalso.
        assert (x / p <= x / j).
        {
          apply Z.div_le_lower_bound.
          - lia.
          - assert (0 <= x / p) by (apply Z.div_pos; lia).
            assert (j * (x / p) <= p * (x / p)).
            { apply Z.mul_le_mono_nonneg_r; lia. }
            pose proof (Z.mul_div_le x p ltac:(lia)).
            nia.
        }
        lia.
    }
    specialize (Hnodiv Hflag p ltac:(lia)).
    exfalso.
    apply Hnodiv.
    apply Z.mod_divide.
    + lia.
    + exact Hdiv.
Qed.
Lemma prime_scan_state_exit_prime_intmax : forall x j flag,
  prime_scan_state x j flag ->
  flag <> 0 ->
  j >= INT_MAX ->
  prime x.
Proof.
  intros x j flag Hstate Hflag Hjmax.
  eapply prime_scan_state_exit_prime; eauto.
  unfold prime_scan_state in Hstate.
  destruct Hstate as [Hx [Hj _]].
  assert (x / j <= 1).
  {
    apply Z.div_le_upper_bound; nia.
  }
  lia.
Qed.
Lemma sum_digits_fuel_zero : forall fuel,
  sum_digits_fuel 0 fuel = 0.
Proof.
  induction fuel; simpl; auto.
Qed.
Lemma sum_digits_fuel_nonneg : forall n fuel,
  0 <= sum_digits_fuel n fuel.
Proof.
  intros n fuel.
  revert n.
  induction fuel; intros n; simpl.
  - lia.
  - destruct (Z.leb n 0) eqn:Hleb.
    + lia.
    + apply Z.leb_gt in Hleb.
      pose proof (IHfuel (n / 10)) as Hrec.
      assert (0 <= n mod 10 < 10) by (apply Z.mod_pos_bound; lia).
      lia.
Qed.
Lemma sum_digits_fuel_bound_digits : forall digits fuel n,
  0 <= n < 10 ^ Z.of_nat digits ->
  sum_digits_fuel n fuel <= 9 * Z.of_nat digits.
Proof.
  induction digits as [| digits IH]; intros fuel n Hn.
  - simpl in Hn.
    assert (n = 0) by lia.
    subst n.
    rewrite sum_digits_fuel_zero.
    lia.
  - destruct fuel as [| fuel].
    + simpl. lia.
    + simpl.
      destruct (Z.leb n 0) eqn:Hleb.
      * lia.
      * apply Z.leb_gt in Hleb.
        assert (Hmod : 0 <= n mod 10 < 10) by (apply Z.mod_pos_bound; lia).
        assert (Hdiv : 0 <= n / 10 < 10 ^ Z.of_nat digits).
        {
          split.
          - apply Z.div_pos; lia.
          - replace (Z.of_nat (S digits)) with (Z.of_nat digits + 1) in Hn by lia.
            rewrite Z.pow_add_r in Hn by lia.
            change (10 ^ 1) with 10 in Hn.
            apply Z.div_lt_upper_bound; nia.
        }
        pose proof (IH fuel (n / 10) Hdiv) as Hrec.
        replace (Z.of_nat (S digits)) with (Z.of_nat digits + 1) by lia.
        lia.
Qed.
Lemma digit_sum_rel_of_enough_fuel : forall fuel n,
  0 <= n ->
  (Z.to_nat n <= fuel)%nat ->
  digit_sum_rel n (sum_digits_fuel n fuel).
Proof.
  induction fuel as [| fuel IH]; intros n Hn Henough.
  - assert (n = 0) by lia.
    subst n.
    simpl.
    constructor.
    lia.
  - simpl.
    destruct (Z.leb n 0) eqn:Hleb.
    + apply Z.leb_le in Hleb.
      constructor.
      lia.
    + apply Z.leb_gt in Hleb.
      apply digit_sum_rel_step.
      * lia.
      * apply IH.
        -- apply Z.div_pos; lia.
        -- assert (Hdiv_lt : (Z.to_nat (n / 10) < Z.to_nat n)%nat).
           {
             apply Z2Nat.inj_lt.
             - apply Z.div_pos; lia.
             - lia.
             - apply Z.div_lt; lia.
           }
           lia.
Qed.
Lemma digit_sum_state_init : forall n,
  digit_sum_int_range n ->
  digit_sum_state n n 0.
Proof.
  intros n Hrange.
  unfold digit_sum_int_range, digit_sum_state in *.
  split.
  - lia.
  - exists (Z.to_nat n).
    assert (Hpow: n < 10 ^ Z.of_nat (Z.to_nat n)).
    {
      rewrite Z2Nat.id by lia.
      apply Z.pow_gt_lin_r; lia.
    }
    assert (Hsum: sum_digits_fuel n (Z.to_nat n) <= 100).
    {
      pose proof (sum_digits_fuel_bound_digits 10 (Z.to_nat n) n) as Hup.
      change (10 ^ Z.of_nat 10) with 10000000000 in Hup.
      specialize (Hup ltac:(lia)).
      change (9 * Z.of_nat 10) with 90 in Hup.
      lia.
    }
    repeat split; try lia.
Qed.
Lemma digit_sum_state_step : forall original current sum,
  digit_sum_state original current sum ->
  current > 0 ->
  digit_sum_state original (current / 10) (sum + current mod 10).
Proof.
  intros original current sum Hstate Hpos.
  unfold digit_sum_state in *.
  destruct Hstate as [Horig [fuel [Hcur [Hsum [Hpow [Hbound Heq]]]]]].
  assert (Hfuel_pos: fuel <> O).
  {
    intro Hfuel0.
    subst fuel.
    simpl in Hpow.
    lia.
  }
  destruct fuel.
  - contradiction.
  - assert (Hdiv_nonneg: 0 <= current / 10) by (apply Z.div_pos; lia).
    assert (Hmod_bounds: 0 <= current mod 10 < 10) by (apply Z.mod_pos_bound; lia).
    assert (Hpow_step: current / 10 < 10 ^ Z.of_nat fuel).
    {
      assert (Hcur_lt: current < 10 * (10 ^ Z.of_nat fuel)).
      {
        replace (Z.of_nat (S fuel)) with (Z.of_nat fuel + 1) in Hpow by lia.
        rewrite Z.pow_add_r in Hpow by lia.
        change (10 ^ 1) with 10 in Hpow.
        lia.
      }
      apply Z.div_lt_upper_bound; nia.
    }
    assert (Hunfold:
      sum_digits_fuel current (S fuel) =
        current mod 10 + sum_digits_fuel (current / 10) fuel).
    {
      simpl.
      assert (Hleb: (current <=? 0) = false).
      { apply Z.leb_gt. lia. }
      rewrite Hleb.
      reflexivity.
    }
    split.
    + exact Horig.
    + exists fuel.
      split.
      * lia.
      * split.
        -- lia.
        -- split.
           ++ exact Hpow_step.
           ++ split.
              ** rewrite Hunfold in Hbound.
                 lia.
              ** rewrite <- Heq.
                 rewrite Hunfold.
                 ring.
Qed.
Lemma Znth_In_range_94 : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma In_Znth_exists_94 : forall (x : Z) l,
  In x l ->
  exists i, 0 <= i < Zlength l /\ Znth i l 0 = x.
Proof.
  intros x l Hin.
  apply In_nth_error in Hin.
  destruct Hin as [n Hn].
  exists (Z.of_nat n).
  split.
  - assert ((n < length l)%nat) as Hlt.
    { apply nth_error_Some. rewrite Hn. discriminate. }
    rewrite Zlength_correct.
    lia.
  - unfold Znth.
    rewrite Nat2Z.id.
    apply nth_error_nth with (d := 0) in Hn.
    exact Hn.
Qed.
Lemma digit_sum_state_done_rel : forall original out,
  digit_sum_state original 0 out ->
  digit_sum_rel original out.
Proof.
  intros original out Hstate.
  unfold digit_sum_state in Hstate.
  destruct Hstate as [Horig [fuel [_ [Hout [_ [_ Heq]]]]]].
  rewrite sum_digits_fuel_zero in Heq.
  assert (out = sum_digits_fuel original (Z.to_nat original)) by lia.
  subst out.
  apply digit_sum_rel_of_enough_fuel.
  - lia.
  - lia.
Qed.
Lemma problem_94_spec_of_digit_state : forall lst largest out,
  list_nonneg_int_range lst ->
  largest_prime_prefix (Zlength lst) lst largest ->
  digit_sum_int_range largest ->
  digit_sum_state largest 0 out ->
  problem_94_spec lst out.
Proof.
  intros lst largest out Hlst_range Hpref Hrange Hstate.
  unfold largest_prime_prefix in Hpref.
  destruct Hpref as [Hbounds [Hlargest Hcase]].
  destruct Hcase as [[Hzero Hnone] | [Hprime [Hin Hmax]]].
  - right.
    split.
    + intros x Hx Hprime_x.
      destruct (In_Znth_exists_94 x lst Hx) as [k [Hk Hval]].
      apply (Hnone k).
      * lia.
      * rewrite Hval. exact Hprime_x.
    + subst largest.
      pose proof (digit_sum_state_done_rel 0 out Hstate).
      inversion H; subst; lia.
  - left.
    exists largest.
    split.
    + destruct Hin as [k [Hk Hval]].
      rewrite Hval.
      apply Znth_In_range_94.
      lia.
    + split.
      * exact Hprime.
      * split.
        -- intros p' Hp' Hprime_p'.
           destruct (In_Znth_exists_94 p' lst Hp') as [k [Hk Hval]].
           assert (Hprime_k : prime (Znth k lst 0)).
           { rewrite Hval. exact Hprime_p'. }
           pose proof (Hmax k Hk Hprime_k).
           lia.
        -- apply digit_sum_state_done_rel.
           exact Hstate.
Qed.


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

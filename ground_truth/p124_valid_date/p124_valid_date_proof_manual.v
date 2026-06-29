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
From SimpleC.EE.CAV.ground_truth_p124_valid_date Require Import p124_valid_date_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
From AUXLib Require Import ListLib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.

Import naive_C_Rules.
Require Import string_bridge.
Require Import p124_valid_date.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p124_valid_date.v so public contract files expose definitions only. *)

Lemma date_prefix_valid_0 : forall l,
  date_prefix_valid 0 l.
Proof.
  unfold date_prefix_valid.
  intros l k Hk.
  lia.
Qed.
Lemma date_prefix_valid_step_sep : forall i l,
  0 <= i ->
  date_prefix_valid i l ->
  (i = 2 \/ i = 5) ->
  Znth i l 0 = 45 ->
  date_prefix_valid (i + 1) l.
Proof.
  unfold date_prefix_valid, date_char_valid.
  intros i l Hi Hpre Hsep Hchar k Hk.
  destruct (Z.eq_dec k i) as [-> | Hne].
  - destruct Hsep as [-> | ->]; simpl; exact Hchar.
  - apply Hpre; lia.
Qed.
Lemma date_prefix_valid_step_digit : forall i l,
  0 <= i ->
  date_prefix_valid i l ->
  i <> 2 ->
  i <> 5 ->
  is_digit (Znth i l 0) ->
  date_prefix_valid (i + 1) l.
Proof.
  unfold date_prefix_valid, date_char_valid.
  intros i l Hi Hpre H2 H5 Hdigit k Hk.
  destruct (Z.eq_dec k i) as [-> | Hne].
  - replace (Z.eqb i 2) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.eqb i 5) with false by (symmetry; apply Z.eqb_neq; lia).
    exact Hdigit.
  - apply Hpre; lia.
Qed.
Lemma date_prefix_valid_10_format : forall l,
  Zlength l = 10 ->
  date_prefix_valid 10 l ->
  date_format l.
Proof.
  intros l Hlen Hpre.
  unfold date_format.
  repeat split; try assumption.
  - specialize (Hpre 2 ltac:(lia)).
    unfold date_char_valid in Hpre.
    simpl in Hpre.
    exact Hpre.
  - specialize (Hpre 5 ltac:(lia)).
    unfold date_char_valid in Hpre.
    simpl in Hpre.
    exact Hpre.
  - specialize (Hpre 0 ltac:(lia)); unfold date_char_valid, is_digit in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 0 ltac:(lia)); unfold date_char_valid, is_digit in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 1 ltac:(lia)); unfold date_char_valid, is_digit in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 1 ltac:(lia)); unfold date_char_valid, is_digit in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 3 ltac:(lia)); unfold date_char_valid, is_digit in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 3 ltac:(lia)); unfold date_char_valid, is_digit in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 4 ltac:(lia)); unfold date_char_valid, is_digit in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 4 ltac:(lia)); unfold date_char_valid, is_digit in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 6 ltac:(lia)); unfold date_char_valid, is_digit in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 6 ltac:(lia)); unfold date_char_valid, is_digit in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 7 ltac:(lia)); unfold date_char_valid, is_digit in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 7 ltac:(lia)); unfold date_char_valid, is_digit in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 8 ltac:(lia)); unfold date_char_valid, is_digit in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 8 ltac:(lia)); unfold date_char_valid, is_digit in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 9 ltac:(lia)); unfold date_char_valid, is_digit in Hpre; simpl in Hpre; lia.
  - specialize (Hpre 9 ltac:(lia)); unfold date_char_valid, is_digit in Hpre; simpl in Hpre; lia.
Qed.
Lemma date_prefix_valid_digit_at : forall i l k,
  date_prefix_valid i l ->
  0 <= k < i ->
  k <> 2 ->
  k <> 5 ->
  is_digit (Znth k l 0).
Proof.
  intros i l k Hpre Hk H2 H5.
  specialize (Hpre k Hk).
  unfold date_char_valid in Hpre.
  replace (Z.eqb k 2) with false in Hpre by (symmetry; apply Z.eqb_neq; lia).
  replace (Z.eqb k 5) with false in Hpre by (symmetry; apply Z.eqb_neq; lia).
  exact Hpre.
Qed.
Lemma valid_date_format : forall l,
  valid_date l -> date_format l.
Proof.
  intros l H.
  unfold valid_date in H.
  tauto.
Qed.
Lemma valid_date_len : forall l,
  valid_date l -> Zlength l = 10.
Proof.
  intros l H.
  destruct (valid_date_format l H) as [Hlen _].
  exact Hlen.
Qed.
Lemma valid_date_sep_at : forall l i,
  valid_date l ->
  (i = 2 \/ i = 5) ->
  Znth i l 0 = 45.
Proof.
  intros l i Hvalid Hsep.
  destruct (valid_date_format l Hvalid) as
    [_ [H2 [H5 _]]].
  destruct Hsep as [-> | ->]; assumption.
Qed.
Lemma valid_date_digit_at : forall l i,
  valid_date l ->
  0 <= i < 10 ->
  i <> 2 ->
  i <> 5 ->
  is_digit (Znth i l 0).
Proof.
  intros l i Hvalid Hi H2 H5.
  destruct (valid_date_format l Hvalid) as
    [_ [_ [_ [H0 [H1 [H3 [H4 [H6 [H7 [H8 H9]]]]]]]]]].
  assert (i = 0 \/ i = 1 \/ i = 3 \/ i = 4 \/
          i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; assumption.
Qed.
Lemma valid_date_month : forall l,
  valid_date l -> 1 <= month l <= 12.
Proof.
  intros l H.
  unfold valid_date in H.
  tauto.
Qed.
Lemma valid_date_day : forall l,
  valid_date l -> 1 <= day l <= days_in_month (month l).
Proof.
  intros l H.
  unfold valid_date in H.
  tauto.
Qed.
Lemma days_in_month_31_bad : forall m,
  (m = 4 \/ m = 6 \/ m = 9 \/ m = 11 \/ m = 2) ->
  days_in_month m < 31.
Proof.
  intros m Hm.
  unfold days_in_month.
  destruct Hm as [-> | [-> | [-> | [-> | ->]]]]; reflexivity.
Qed.
Lemma days_in_month_feb_lt_30 :
  days_in_month 2 < 30.
Proof.
  unfold days_in_month.
  reflexivity.
Qed.
Lemma days_in_month_le_31 : forall m,
  days_in_month m <= 31.
Proof.
  intro m.
  unfold days_in_month.
  destruct (Z.eqb m 1); destruct (Z.eqb m 3); destruct (Z.eqb m 5);
  destruct (Z.eqb m 7); destruct (Z.eqb m 8); destruct (Z.eqb m 10);
  destruct (Z.eqb m 12); destruct (Z.eqb m 4); destruct (Z.eqb m 6);
  destruct (Z.eqb m 9); destruct (Z.eqb m 11); destruct (Z.eqb m 2);
  simpl; lia.
Qed.
Lemma valid_date_intro_from_checks : forall l,
  date_format l ->
  1 <= month l <= 12 ->
  1 <= day l <= 31 ->
  ~(day l = 31 /\
    (month l = 4 \/ month l = 6 \/ month l = 9 \/
     month l = 11 \/ month l = 2)) ->
  ~(day l = 30 /\ month l = 2) ->
  valid_date l.
Proof.
  intros l Hfmt Hmonth Hday Hnot31 HnotFeb30.
  unfold valid_date.
  split; [exact Hfmt |].
  split; [exact Hmonth |].
  unfold days_in_month.
  assert (month l = 1 \/ month l = 2 \/ month l = 3 \/
          month l = 4 \/ month l = 5 \/ month l = 6 \/
          month l = 7 \/ month l = 8 \/ month l = 9 \/
          month l = 10 \/ month l = 11 \/ month l = 12) by lia.
  destruct H as [Hm | [Hm | [Hm | [Hm | [Hm | [Hm | [Hm | [Hm | [Hm | [Hm | [Hm | Hm]]]]]]]]]]];
    rewrite Hm; simpl in *; lia.
Qed.
Lemma ascii_of_inj_const_124 : forall x n,
  0 <= x < 256 ->
  (n < 256)%nat ->
  ascii_of x = ascii_of_nat n ->
  x = Z.of_nat n.
Proof.
  intros x n Hx Hn Heq.
  apply (f_equal nat_of_ascii) in Heq.
  unfold ascii_of in Heq.
  rewrite nat_ascii_embedding in Heq by lia.
  rewrite nat_ascii_embedding in Heq by lia.
  lia.
Qed.
Lemma nat_of_digit_ascii_of : forall x,
  is_digit x ->
  nat_of_digit (ascii_of x) = Some (Z.to_nat (x - 48)).
Proof.
  intros x Hdigit.
  unfold is_digit in Hdigit.
  assert (x = 48 \/ x = 49 \/ x = 50 \/ x = 51 \/ x = 52 \/
          x = 53 \/ x = 54 \/ x = 55 \/ x = 56 \/ x = 57) by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
    reflexivity.
Qed.
Lemma nat_of_digit_ascii_of_inv : forall x d,
  0 <= x < 256 ->
  nat_of_digit (ascii_of x) = Some d ->
  is_digit x /\ d = Z.to_nat (x - 48).
Proof.
  intros x d Hrange Hdigit.
  assert (Hcase :
    ascii_of x = "0"%char \/ ascii_of x = "1"%char \/
    ascii_of x = "2"%char \/ ascii_of x = "3"%char \/
    ascii_of x = "4"%char \/ ascii_of x = "5"%char \/
    ascii_of x = "6"%char \/ ascii_of x = "7"%char \/
    ascii_of x = "8"%char \/ ascii_of x = "9"%char).
  {
    remember (ascii_of x) as c.
    destruct c as [[] [] [] [] [] [] [] []]; simpl in Hdigit; try discriminate;
      repeat (first [left; subst; reflexivity | right]); subst; reflexivity.
  }
  destruct Hcase as [E | [E | [E | [E | [E | [E | [E | [E | [E | E]]]]]]]]].
  - rewrite E in Hdigit. inversion Hdigit; subst; clear Hdigit.
    apply ascii_of_inj_const_124 with (n := 48%nat) in E; try lia.
    subst; split; [unfold is_digit; lia | reflexivity].
  - rewrite E in Hdigit. inversion Hdigit; subst; clear Hdigit.
    apply ascii_of_inj_const_124 with (n := 49%nat) in E; try lia.
    subst; split; [unfold is_digit; lia | reflexivity].
  - rewrite E in Hdigit. inversion Hdigit; subst; clear Hdigit.
    apply ascii_of_inj_const_124 with (n := 50%nat) in E; try lia.
    subst; split; [unfold is_digit; lia | reflexivity].
  - rewrite E in Hdigit. inversion Hdigit; subst; clear Hdigit.
    apply ascii_of_inj_const_124 with (n := 51%nat) in E; try lia.
    subst; split; [unfold is_digit; lia | reflexivity].
  - rewrite E in Hdigit. inversion Hdigit; subst; clear Hdigit.
    apply ascii_of_inj_const_124 with (n := 52%nat) in E; try lia.
    subst; split; [unfold is_digit; lia | reflexivity].
  - rewrite E in Hdigit. inversion Hdigit; subst; clear Hdigit.
    apply ascii_of_inj_const_124 with (n := 53%nat) in E; try lia.
    subst; split; [unfold is_digit; lia | reflexivity].
  - rewrite E in Hdigit. inversion Hdigit; subst; clear Hdigit.
    apply ascii_of_inj_const_124 with (n := 54%nat) in E; try lia.
    subst; split; [unfold is_digit; lia | reflexivity].
  - rewrite E in Hdigit. inversion Hdigit; subst; clear Hdigit.
    apply ascii_of_inj_const_124 with (n := 55%nat) in E; try lia.
    subst; split; [unfold is_digit; lia | reflexivity].
  - rewrite E in Hdigit. inversion Hdigit; subst; clear Hdigit.
    apply ascii_of_inj_const_124 with (n := 56%nat) in E; try lia.
    subst; split; [unfold is_digit; lia | reflexivity].
  - rewrite E in Hdigit. inversion Hdigit; subst; clear Hdigit.
    apply ascii_of_inj_const_124 with (n := 57%nat) in E; try lia.
    subst; split; [unfold is_digit; lia | reflexivity].
Qed.
Lemma nat_of_2_digits_ascii_of : forall x y,
  is_digit x ->
  is_digit y ->
  nat_of_2_digits (ascii_of x) (ascii_of y) =
    Some (Z.to_nat ((x - 48) * 10 + (y - 48))).
Proof.
  intros x y Hx Hy.
  unfold nat_of_2_digits.
  rewrite nat_of_digit_ascii_of by exact Hx.
  rewrite nat_of_digit_ascii_of by exact Hy.
  f_equal.
  unfold is_digit in *.
  rewrite Z2Nat.inj_add by lia.
  rewrite Z2Nat.inj_mul by lia.
  lia.
Qed.
Lemma nat_of_4_digits_ascii_of : forall a b c d,
  is_digit a ->
  is_digit b ->
  is_digit c ->
  is_digit d ->
  nat_of_4_digits (ascii_of a) (ascii_of b) (ascii_of c) (ascii_of d) =
    Some (Z.to_nat ((a - 48) * 1000 + (b - 48) * 100 + (c - 48) * 10 + (d - 48))).
Proof.
  intros a b c d Ha Hb Hc Hd.
  unfold nat_of_4_digits.
  rewrite nat_of_digit_ascii_of by exact Ha.
  rewrite nat_of_digit_ascii_of by exact Hb.
  rewrite nat_of_digit_ascii_of by exact Hc.
  rewrite nat_of_digit_ascii_of by exact Hd.
  f_equal.
  unfold is_digit in *.
  repeat rewrite Z2Nat.inj_add by lia.
  repeat rewrite Z2Nat.inj_mul by lia.
  lia.
Qed.
Lemma days_in_month_nat_correct_124 : forall m,
  1 <= m <= 12 ->
  Z.of_nat (days_in_month_nat (Z.to_nat m)) = days_in_month m.
Proof.
  intros m Hm.
  assert (m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6 \/
          m = 7 \/ m = 8 \/ m = 9 \/ m = 10 \/ m = 11 \/ m = 12) by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]];
    reflexivity.
Qed.
Ltac destruct_date_list l :=
  destruct l as [| z0 [| z1 [| z2 [| z3 [| z4 [| z5 [| z6 [| z7 [| z8 [| z9 [| extra]]]]]]]]]]];
  simpl in *; try repeat rewrite Zlength_cons in *; try rewrite Zlength_nil in *;
  simpl in *;
  try match goal with
      | H : context[Zlength ?xs] |- _ => pose proof (Zlength_nonneg xs); lia
      end;
  try lia.
Lemma valid_date_to_problem_124_spec : forall l,
  ascii_range l ->
  valid_date l ->
  problem_124_spec l 1.
Proof.
  intros l Hrange Hvalid.
  destruct Hvalid as [Hfmt [Hmonth Hday]].
  unfold date_format in Hfmt.
  destruct Hfmt as
    [Hlen [Hsep2 [Hsep5 [H0 [H1 [H3 [H4 [H6 [H7 [H8 H9]]]]]]]]]].
  destruct_date_list l.
  simpl in Hsep2, Hsep5.
  change (z2 = 45) in Hsep2.
  change (z5 = 45) in Hsep5.
  change (is_digit z0) in H0.
  change (is_digit z1) in H1.
  change (is_digit z3) in H3.
  change (is_digit z4) in H4.
  change (is_digit z6) in H6.
  change (is_digit z7) in H7.
  change (is_digit z8) in H8.
  change (is_digit z9) in H9.
  unfold problem_124_spec.
  split; intros _.
  {
  simpl.
  repeat split.
  - rewrite Hsep2. reflexivity.
  - rewrite Hsep5. reflexivity.
  - exists (Z.to_nat (month [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9])).
    exists (Z.to_nat (day [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9])).
    exists (Z.to_nat (year [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9])).
    repeat split.
    + unfold month.
      simpl.
      apply nat_of_2_digits_ascii_of; assumption.
    + unfold day.
      simpl.
      apply nat_of_2_digits_ascii_of; assumption.
    + unfold year.
      simpl.
      apply nat_of_4_digits_ascii_of; assumption.
    + replace 1%nat with (Z.to_nat 1) by reflexivity.
      apply Z2Nat.inj_le; lia.
    + replace 12%nat with (Z.to_nat 12) by reflexivity.
      apply Z2Nat.inj_le; lia.
    + replace 1%nat with (Z.to_nat 1) by reflexivity.
      apply Z2Nat.inj_le; lia.
    + apply Nat2Z.inj_le.
      rewrite Z2Nat.id by lia.
      rewrite days_in_month_nat_correct_124 by exact Hmonth.
      apply Hday.
  }
  { reflexivity. }
Qed.
Lemma problem_124_spec_to_valid_date : forall l,
  ascii_range l ->
  problem_124_spec l 1 ->
  valid_date l.
Proof.
  intros l Hrange Hspec.
  unfold problem_124_spec in Hspec.
  destruct Hspec as [Hspec _].
  specialize (Hspec eq_refl).
  destruct_date_list l.
  destruct Hspec as [Hsep2 [Hsep5 [m [d [y [Hm [Hd [Hy [Hmonth Hday]]]]]]]]].
  assert (Hz2 : z2 = 45).
  {
    apply ascii_of_inj_const_124 with (n := 45%nat); try lia.
    - pose proof (Hrange 2 ltac:(change (0 <= 2 < 10); lia)) as Hz2range. exact Hz2range.
    - exact Hsep2.
  }
  assert (Hz5 : z5 = 45).
  {
    apply ascii_of_inj_const_124 with (n := 45%nat); try lia.
    - pose proof (Hrange 5 ltac:(change (0 <= 5 < 10); lia)) as Hz5range. exact Hz5range.
    - exact Hsep5.
  }
  unfold nat_of_2_digits in Hm.
  unfold nat_of_2_digits in Hd.
  unfold nat_of_4_digits in Hy.
  destruct (nat_of_digit (ascii_of z0)) as [d0|] eqn:Hz0; try discriminate.
  destruct (nat_of_digit (ascii_of z1)) as [d1|] eqn:Hz1; try discriminate.
  destruct (nat_of_digit (ascii_of z3)) as [d3|] eqn:Hz3; try discriminate.
  destruct (nat_of_digit (ascii_of z4)) as [d4|] eqn:Hz4; try discriminate.
  destruct (nat_of_digit (ascii_of z6)) as [d6|] eqn:Hz6; try discriminate.
  destruct (nat_of_digit (ascii_of z7)) as [d7|] eqn:Hz7; try discriminate.
  destruct (nat_of_digit (ascii_of z8)) as [d8|] eqn:Hz8; try discriminate.
  destruct (nat_of_digit (ascii_of z9)) as [d9|] eqn:Hz9; try discriminate.
  inversion Hm; subst m; clear Hm.
  inversion Hd; subst d; clear Hd.
  inversion Hy; subst y; clear Hy.
  change (1 <= 10 * d0 + d1 <= 12)%nat in Hmonth.
  change (1 <= 10 * d3 + d4 <= days_in_month_nat (10 * d0 + d1))%nat in Hday.
  pose proof (Hrange 0 ltac:(change (0 <= 0 < 10); lia)) as Hr0.
  pose proof (Hrange 1 ltac:(change (0 <= 1 < 10); lia)) as Hr1.
  pose proof (Hrange 3 ltac:(change (0 <= 3 < 10); lia)) as Hr3.
  pose proof (Hrange 4 ltac:(change (0 <= 4 < 10); lia)) as Hr4.
  pose proof (Hrange 6 ltac:(change (0 <= 6 < 10); lia)) as Hr6.
  pose proof (Hrange 7 ltac:(change (0 <= 7 < 10); lia)) as Hr7.
  pose proof (Hrange 8 ltac:(change (0 <= 8 < 10); lia)) as Hr8.
  pose proof (Hrange 9 ltac:(change (0 <= 9 < 10); lia)) as Hr9.
  change (0 <= z0 < 256) in Hr0.
  change (0 <= z1 < 256) in Hr1.
  change (0 <= z3 < 256) in Hr3.
  change (0 <= z4 < 256) in Hr4.
  change (0 <= z6 < 256) in Hr6.
  change (0 <= z7 < 256) in Hr7.
  change (0 <= z8 < 256) in Hr8.
  change (0 <= z9 < 256) in Hr9.
  pose proof (nat_of_digit_ascii_of_inv z0 d0 Hr0 Hz0) as [Hz0d Hz0v].
  pose proof (nat_of_digit_ascii_of_inv z1 d1 Hr1 Hz1) as [Hz1d Hz1v].
  pose proof (nat_of_digit_ascii_of_inv z3 d3 Hr3 Hz3) as [Hz3d Hz3v].
  pose proof (nat_of_digit_ascii_of_inv z4 d4 Hr4 Hz4) as [Hz4d Hz4v].
  pose proof (nat_of_digit_ascii_of_inv z6 d6 Hr6 Hz6) as [Hz6d Hz6v].
  pose proof (nat_of_digit_ascii_of_inv z7 d7 Hr7 Hz7) as [Hz7d Hz7v].
  pose proof (nat_of_digit_ascii_of_inv z8 d8 Hr8 Hz8) as [Hz8d Hz8v].
  pose proof (nat_of_digit_ascii_of_inv z9 d9 Hr9 Hz9) as [Hz9d Hz9v].
  assert (HmonthZ : 1 <= Z.of_nat (10 * d0 + d1) <= 12) by lia.
  rewrite Nat2Z.inj_add, Nat2Z.inj_mul in HmonthZ.
  rewrite Hz0v, Hz1v in HmonthZ.
  repeat rewrite Z2Nat.id in HmonthZ by (unfold is_digit in *; lia).
  change (1 <= 10 * (z0 - 48) + (z1 - 48) <= 12) in HmonthZ.
  assert (HdayZ : 1 <= Z.of_nat (10 * d3 + d4) <=
                    Z.of_nat (days_in_month_nat (10 * d0 + d1))) by lia.
  rewrite Nat2Z.inj_add, Nat2Z.inj_mul in HdayZ.
  rewrite Hz3v, Hz4v in HdayZ.
  repeat rewrite Z2Nat.id in HdayZ by (unfold is_digit in *; lia).
  change (1 <= 10 * (z3 - 48) + (z4 - 48) <=
          Z.of_nat (days_in_month_nat (10 * d0 + d1))) in HdayZ.
  replace (Z.of_nat (days_in_month_nat (10 * d0 + d1)))
    with (days_in_month ((z0 - 48) * 10 + (z1 - 48))) in HdayZ.
  2:{
    rewrite Hz0v, Hz1v.
    replace (10 * Z.to_nat (z0 - 48) + Z.to_nat (z1 - 48))%nat
      with (Z.to_nat ((z0 - 48) * 10 + (z1 - 48))).
    rewrite days_in_month_nat_correct_124 by lia.
    reflexivity.
    rewrite Z2Nat.inj_add by (unfold is_digit in *; lia).
    rewrite Z2Nat.inj_mul by (unfold is_digit in *; lia).
    lia.
  }
  unfold valid_date, date_format, month, day.
  simpl.
  change (Znth 0 [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9] 0) with z0 in *.
  change (Znth 1 [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9] 0) with z1 in *.
  change (Znth 2 [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9] 0) with z2 in *.
  change (Znth 3 [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9] 0) with z3 in *.
  change (Znth 4 [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9] 0) with z4 in *.
  change (Znth 5 [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9] 0) with z5 in *.
  change (Znth 6 [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9] 0) with z6 in *.
  change (Znth 7 [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9] 0) with z7 in *.
  change (Znth 8 [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9] 0) with z8 in *.
  change (Znth 9 [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9] 0) with z9 in *.
  repeat split;
    repeat rewrite Znth_cons by lia;
    unfold is_digit in *; subst; try lia; try reflexivity.
Qed.
Lemma problem_124_spec_true : forall l,
  ascii_range l ->
  valid_date l ->
  problem_124_spec l 1.
Proof.
  intros l Hrange H.
  unfold problem_124_spec.
  split; intros _.
  - pose proof (valid_date_to_problem_124_spec l Hrange H) as Hspec.
    unfold problem_124_spec in Hspec.
    apply Hspec.
    reflexivity.
  - reflexivity.
Qed.
Lemma problem_124_spec_false : forall l,
  ascii_range l ->
  ~ valid_date l ->
  problem_124_spec l 0.
Proof.
  intros l Hrange H.
  unfold problem_124_spec.
  split; intros Hbad.
  - lia.
  - exfalso.
    apply H.
    apply problem_124_spec_to_valid_date; [assumption |].
    unfold problem_124_spec.
    split; intros _; [exact Hbad | reflexivity].
Qed.


Ltac date_pre :=
  pre_process;
  repeat rewrite app_Znth1 in * by lia.

Ltac solve_date_simple :=
  date_pre;
  try match goal with Hpre : date_prefix_valid ?i ?l |- context[Znth 0 ?l 0] =>
    pose proof (date_prefix_valid_digit_at i l 0 Hpre ltac:(lia) ltac:(lia) ltac:(lia)); unfold is_digit in *
  end;
  try match goal with Hpre : date_prefix_valid ?i ?l |- context[Znth 1 ?l 0] =>
    pose proof (date_prefix_valid_digit_at i l 1 Hpre ltac:(lia) ltac:(lia) ltac:(lia)); unfold is_digit in *
  end;
  try match goal with Hpre : date_prefix_valid ?i ?l |- context[Znth 3 ?l 0] =>
    pose proof (date_prefix_valid_digit_at i l 3 Hpre ltac:(lia) ltac:(lia) ltac:(lia)); unfold is_digit in *
  end;
  try match goal with Hpre : date_prefix_valid ?i ?l |- context[Znth 4 ?l 0] =>
    pose proof (date_prefix_valid_digit_at i l 4 Hpre ltac:(lia) ltac:(lia) ltac:(lia)); unfold is_digit in *
  end;
  entailer!; try lia.

Ltac solve_date_false :=
  date_pre; entailer!;
  try solve [auto | lia];
  match goal with
  | Hrange : ascii_range ?l |- problem_124_spec ?l 0 =>
      apply (problem_124_spec_false l Hrange)
  end;
  intro;
  match goal with Hvalid : valid_date ?l |- _ =>
  first [
    pose proof (valid_date_len _ Hvalid); lia
  | match goal with
  | Hbad : Znth ?i ?l 0 <> 45, Hi : ?i = 2 |- _ =>
      pose proof (valid_date_sep_at l i Hvalid (or_introl eq_refl)); lia
  | Hbad : Znth ?i ?l 0 <> 45, Hi : ?i = 5 |- _ =>
      pose proof (valid_date_sep_at l i Hvalid (or_intror eq_refl)); lia
    end
  | match goal with
  | Hbad : Znth ?i ?l 0 < 48 |- _ =>
      pose proof (valid_date_digit_at l i Hvalid ltac:(lia) ltac:(lia) ltac:(lia));
      unfold is_digit in *; lia
  | Hbad : Znth ?i ?l 0 > 57 |- _ =>
      pose proof (valid_date_digit_at l i Hvalid ltac:(lia) ltac:(lia) ltac:(lia));
      unfold is_digit in *; lia
    end
  | pose proof (valid_date_month _ Hvalid) as Hmonth_valid;
    pose proof (valid_date_day _ Hvalid) as Hday_valid;
    pose proof (days_in_month_le_31 (month l)) as Hdays_le;
    unfold month, day in *;
    repeat rewrite app_Znth1 in * by lia;
    try match goal with
    | Hm : ?m = 4, Hday_valid : context[days_in_month ?m] |- _ =>
        rewrite Hm in Hday_valid; simpl in Hday_valid
    end;
    try match goal with
    | Hm : ?m = 6, Hday_valid : context[days_in_month ?m] |- _ =>
        rewrite Hm in Hday_valid; simpl in Hday_valid
    end;
    try match goal with
    | Hm : ?m = 9, Hday_valid : context[days_in_month ?m] |- _ =>
        rewrite Hm in Hday_valid; simpl in Hday_valid
    end;
    try match goal with
    | Hm : ?m = 11, Hday_valid : context[days_in_month ?m] |- _ =>
        rewrite Hm in Hday_valid; simpl in Hday_valid
    end;
    try match goal with
    | Hm : ?m = 2, Hday_valid : context[days_in_month ?m] |- _ =>
        rewrite Hm in Hday_valid; simpl in Hday_valid
    end;
    lia
  ]
  end.

Ltac solve_date_true :=
  date_pre; entailer!;
  try solve [auto | lia];
  try match goal with
  | Hge : ?i >= 10, Hle : ?i <= 10 |- _ =>
      assert (i = 10) by lia; subst i
  end;
  try solve [auto | lia];
  match goal with
  | Hrange : ascii_range ?l |- problem_124_spec ?l 1 =>
      apply (problem_124_spec_true l Hrange)
  end;
  apply valid_date_intro_from_checks;
  [ apply date_prefix_valid_10_format; [lia | assumption]
  | unfold month; lia
  | unfold day; lia
  | unfold month, day; intro;
    match goal with Hbad : _ /\ _ |- _ => destruct Hbad as [? ?]; lia end
  | unfold month, day; intro;
    match goal with Hbad : _ /\ _ |- _ => destruct Hbad as [? ?]; lia end
  ].

Ltac solve_date_bad_day_month :=
  date_pre; entailer!;
  try solve [auto | lia];
  match goal with
  | Hrange : ascii_range ?l |- problem_124_spec ?l 0 =>
      apply (problem_124_spec_false l Hrange)
  end;
  intro;
  match goal with Hvalid : valid_date _ |- _ =>
    let Hday := fresh "Hday_valid" in
    pose proof (valid_date_day _ Hvalid) as Hday;
    unfold month, day in Hday;
    try match goal with H : ?d = 30 |- _ => rewrite H in Hday end;
    try match goal with H : ?d = 31 |- _ => rewrite H in Hday end;
    try match goal with H : ?m = 2 |- _ => rewrite H in Hday end;
    try match goal with H : ?m = 4 |- _ => rewrite H in Hday end;
    try match goal with H : ?m = 6 |- _ => rewrite H in Hday end;
    try match goal with H : ?m = 9 |- _ => rewrite H in Hday end;
    try match goal with H : ?m = 11 |- _ => rewrite H in Hday end;
    unfold days_in_month in Hday;
    simpl in Hday;
    lia
  end.

Ltac solve_date_bad_sep :=
  date_pre; entailer!;
  try solve [auto | lia];
  match goal with
  | Hrange : ascii_range ?l |- problem_124_spec ?l 0 =>
      apply (problem_124_spec_false l Hrange)
  end;
  intro;
  match goal with Hvalid : valid_date ?l |- _ =>
    match goal with
    | Hbad : Znth ?i ?l' 0 <> 45, Hi : ?i = 2 |- _ =>
        unify l l';
        pose proof (valid_date_sep_at l i Hvalid (or_introl eq_refl)); lia
    | Hbad : Znth ?i ?l' 0 <> 45, Hi : ?i = 5 |- _ =>
        unify l l';
        pose proof (valid_date_sep_at l i Hvalid (or_intror eq_refl)); lia
    end
  end.

Lemma proof_of_p124_valid_date_safety_wit_18 : p124_valid_date_safety_wit_18.
Proof. unfold p124_valid_date_safety_wit_18; intros; solve_date_simple. Qed.

Lemma proof_of_p124_valid_date_safety_wit_19 : p124_valid_date_safety_wit_19.
Proof. unfold p124_valid_date_safety_wit_19; intros; solve_date_simple. Qed.

Lemma proof_of_p124_valid_date_safety_wit_20 : p124_valid_date_safety_wit_20.
Proof. unfold p124_valid_date_safety_wit_20; intros; solve_date_simple. Qed.

Lemma proof_of_p124_valid_date_safety_wit_21 : p124_valid_date_safety_wit_21.
Proof. unfold p124_valid_date_safety_wit_21; intros; solve_date_simple. Qed.

Lemma proof_of_p124_valid_date_safety_wit_27 : p124_valid_date_safety_wit_27.
Proof. unfold p124_valid_date_safety_wit_27; intros; solve_date_simple. Qed.

Lemma proof_of_p124_valid_date_safety_wit_28 : p124_valid_date_safety_wit_28.
Proof. unfold p124_valid_date_safety_wit_28; intros; solve_date_simple. Qed.

Lemma proof_of_p124_valid_date_safety_wit_29 : p124_valid_date_safety_wit_29.
Proof. unfold p124_valid_date_safety_wit_29; intros; solve_date_simple. Qed.

Lemma proof_of_p124_valid_date_safety_wit_30 : p124_valid_date_safety_wit_30.
Proof. unfold p124_valid_date_safety_wit_30; intros; solve_date_simple. Qed.

Lemma proof_of_p124_valid_date_entail_wit_1 : p124_valid_date_entail_wit_1.
Proof.
  unfold p124_valid_date_entail_wit_1.
  intros.
  date_pre.
  entailer!.
  apply date_prefix_valid_0.
Qed.

Lemma proof_of_p124_valid_date_entail_wit_2_1 : p124_valid_date_entail_wit_2_1.
Proof.
  unfold p124_valid_date_entail_wit_2_1.
  intros.
  date_pre.
  entailer!.
  apply date_prefix_valid_step_sep; auto; lia.
Qed.

Lemma proof_of_p124_valid_date_entail_wit_2_2 : p124_valid_date_entail_wit_2_2.
Proof.
  unfold p124_valid_date_entail_wit_2_2.
  intros.
  date_pre.
  entailer!.
  apply date_prefix_valid_step_sep; auto; lia.
Qed.

Lemma proof_of_p124_valid_date_entail_wit_2_3 : p124_valid_date_entail_wit_2_3.
Proof.
  unfold p124_valid_date_entail_wit_2_3.
  intros.
  date_pre.
  entailer!.
  apply date_prefix_valid_step_digit; auto; unfold is_digit; lia.
Qed.

Lemma proof_of_p124_valid_date_return_wit_1 : p124_valid_date_return_wit_1.
Proof. unfold p124_valid_date_return_wit_1; intros; solve_date_true. Qed.

Lemma proof_of_p124_valid_date_return_wit_2 : p124_valid_date_return_wit_2.
Proof. unfold p124_valid_date_return_wit_2; intros; solve_date_true. Qed.

Lemma proof_of_p124_valid_date_return_wit_3 : p124_valid_date_return_wit_3.
Proof. unfold p124_valid_date_return_wit_3; intros; solve_date_true. Qed.

Lemma proof_of_p124_valid_date_return_wit_4 : p124_valid_date_return_wit_4.
Proof. unfold p124_valid_date_return_wit_4; intros; solve_date_bad_day_month. Qed.

Lemma proof_of_p124_valid_date_return_wit_5 : p124_valid_date_return_wit_5.
Proof. unfold p124_valid_date_return_wit_5; intros; solve_date_bad_day_month. Qed.

Lemma proof_of_p124_valid_date_return_wit_6 : p124_valid_date_return_wit_6.
Proof. unfold p124_valid_date_return_wit_6; intros; solve_date_bad_day_month. Qed.

Lemma proof_of_p124_valid_date_return_wit_7 : p124_valid_date_return_wit_7.
Proof. unfold p124_valid_date_return_wit_7; intros; solve_date_bad_day_month. Qed.

Lemma proof_of_p124_valid_date_return_wit_8 : p124_valid_date_return_wit_8.
Proof. unfold p124_valid_date_return_wit_8; intros; solve_date_bad_day_month. Qed.

Lemma proof_of_p124_valid_date_return_wit_9 : p124_valid_date_return_wit_9.
Proof. unfold p124_valid_date_return_wit_9; intros; solve_date_bad_day_month. Qed.

Lemma proof_of_p124_valid_date_return_wit_10 : p124_valid_date_return_wit_10.
Proof. unfold p124_valid_date_return_wit_10; intros; solve_date_false. Qed.

Lemma proof_of_p124_valid_date_return_wit_11 : p124_valid_date_return_wit_11.
Proof. unfold p124_valid_date_return_wit_11; intros; solve_date_false. Qed.

Lemma proof_of_p124_valid_date_return_wit_12 : p124_valid_date_return_wit_12.
Proof. unfold p124_valid_date_return_wit_12; intros; solve_date_false. Qed.

Lemma proof_of_p124_valid_date_return_wit_13 : p124_valid_date_return_wit_13.
Proof. unfold p124_valid_date_return_wit_13; intros; solve_date_false. Qed.

Lemma proof_of_p124_valid_date_return_wit_14 : p124_valid_date_return_wit_14.
Proof. unfold p124_valid_date_return_wit_14; intros; solve_date_false. Qed.

Lemma proof_of_p124_valid_date_return_wit_15 : p124_valid_date_return_wit_15.
Proof. unfold p124_valid_date_return_wit_15; intros; solve_date_false. Qed.

Lemma proof_of_p124_valid_date_return_wit_16 : p124_valid_date_return_wit_16.
Proof.
  unfold p124_valid_date_return_wit_16.
  intros.
  date_pre; entailer!.
  match goal with
  | Hrange : ascii_range ?l |- problem_124_spec ?l 0 =>
      apply (problem_124_spec_false l Hrange)
  end.
  intro Hvalid.
  pose proof (valid_date_sep_at l i Hvalid (or_intror H0)).
  lia.
Qed.

Lemma proof_of_p124_valid_date_return_wit_17 : p124_valid_date_return_wit_17.
Proof.
  unfold p124_valid_date_return_wit_17.
  intros.
  date_pre; entailer!.
  match goal with
  | Hrange : ascii_range ?l |- problem_124_spec ?l 0 =>
      apply (problem_124_spec_false l Hrange)
  end.
  intro Hvalid.
  pose proof (valid_date_sep_at l i Hvalid (or_introl H0)).
  lia.
Qed.

Lemma proof_of_p124_valid_date_return_wit_18 : p124_valid_date_return_wit_18.
Proof. unfold p124_valid_date_return_wit_18; intros; solve_date_false. Qed.

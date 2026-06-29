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
From SimpleC.EE.CAV.ground_truth_p018_how_many_times Require Import p018_how_many_times_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import List.
Require Import Ascii.
Require Import String.
Require Import Nat.

Import naive_C_Rules.
Require Import p018_how_many_times.
Local Open Scope sac.
Require Import Coq.Strings.Ascii.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope list_scope.

(* Proof helpers moved from p018_how_many_times.v so public contract files expose definitions only. *)

Lemma count_matches_upto_zero : forall input substring,
  count_matches_upto 0 input substring = 0.
Proof. reflexivity. Qed.
Lemma count_matches_upto_nonneg : forall i input substring,
  0 <= count_matches_upto i input substring.
Proof.
  intros i input substring.
  unfold count_matches_upto.
  induction (Z.to_nat i) as [| fuel IH]; simpl; [lia |].
  destruct (match_at_zb (Z.of_nat fuel) input substring); lia.
Qed.
Lemma count_matches_upto_le : forall i input substring,
  0 <= i ->
  count_matches_upto i input substring <= i.
Proof.
  intros i input substring Hi.
  unfold count_matches_upto.
  remember (Z.to_nat i) as fuel.
  assert (Hfuel : Z.of_nat fuel = i) by lia.
  rewrite <- Hfuel.
  clear i Hi Hfuel Heqfuel.
  induction fuel as [| fuel IH]; simpl.
  - lia.
  - destruct (match_at_zb (Z.of_nat fuel) input substring); lia.
Qed.
Lemma count_matches_upto_step : forall i input substring,
  0 <= i ->
  count_matches_upto (i + 1) input substring =
    count_matches_upto i input substring +
    if match_at_zb i input substring then 1 else 0.
Proof.
  intros i input substring Hi.
  unfold count_matches_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.
Lemma count_matches_upto_step_hit : forall i input substring,
  0 <= i ->
  match_at_zb i input substring = true ->
  count_matches_upto (i + 1) input substring =
    count_matches_upto i input substring + 1.
Proof.
  intros i input substring Hi Hhit.
  rewrite count_matches_upto_step by lia.
  rewrite Hhit.
  reflexivity.
Qed.
Lemma count_matches_upto_step_miss : forall i input substring,
  0 <= i ->
  match_at_zb i input substring = false ->
  count_matches_upto (i + 1) input substring =
    count_matches_upto i input substring.
Proof.
  intros i input substring Hi Hmiss.
  rewrite count_matches_upto_step by lia.
  rewrite Hmiss.
  lia.
Qed.
Lemma match_progress_init : forall i input substring,
  match_progress i 0 1 input substring.
Proof.
  unfold match_progress, match_prefix, mismatch_prefix.
  intros.
  split.
  - intros _ k Hk. lia.
  - intros H; discriminate.
Qed.
Lemma match_progress_step_same : forall i j input substring,
  0 <= j ->
  match_progress i j 1 input substring ->
  Znth (i + j) input 0 = Znth j substring 0 ->
  match_progress i (j + 1) 1 input substring.
Proof.
  unfold match_progress, match_prefix, mismatch_prefix.
  intros i j input substring Hj [Hprefix _] Heq.
  split.
  - intros _ k Hk.
    destruct (Z.eq_dec k j) as [-> | Hne].
    + exact Heq.
    + apply Hprefix; lia.
  - intros H; discriminate.
Qed.
Lemma match_progress_step_keep_mismatch : forall i j input substring,
  0 <= j ->
  match_progress i j 0 input substring ->
  match_progress i (j + 1) 0 input substring.
Proof.
  unfold match_progress, match_prefix, mismatch_prefix.
  intros i j input substring Hj [_ Hmis].
  split.
  - intros H; discriminate.
  - intros _. destruct (Hmis eq_refl) as [k [Hk Hneq]].
    exists k. split; [lia | exact Hneq].
Qed.
Lemma match_progress_step_new_mismatch : forall i j input substring,
  0 <= j ->
  Znth (i + j) input 0 <> Znth j substring 0 ->
  match_progress i (j + 1) 0 input substring.
Proof.
  unfold match_progress, match_prefix, mismatch_prefix.
  intros i j input substring Hj Hneq.
  split.
  - intros H; discriminate.
  - intros _. exists j. split; [lia | exact Hneq].
Qed.
Lemma list_eq_zb_true_iff : forall l1 l2,
  list_eq_zb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [| x xs IH]; destruct l2 as [| y ys]; simpl; split; intros H;
    try reflexivity; try discriminate.
  - apply andb_true_iff in H as [Hxy Hxs].
    apply Z.eqb_eq in Hxy.
    apply IH in Hxs.
    congruence.
  - inversion H; subst.
    rewrite Z.eqb_refl.
    rewrite (proj2 (IH ys)); reflexivity.
Qed.
Lemma list_eq_zb_false_neq : forall l1 l2,
  l1 <> l2 ->
  list_eq_zb l1 l2 = false.
Proof.
  intros l1 l2 Hneq.
  destruct (list_eq_zb l1 l2) eqn:H; [| reflexivity].
  apply list_eq_zb_true_iff in H.
  contradiction.
Qed.
Lemma prefix_sublist_eq : forall i j input substring,
  0 <= i ->
  0 <= j ->
  i + j <= Zlength input ->
  j <= Zlength substring ->
  match_prefix i j input substring ->
  sublist i (i + j) input = sublist 0 j substring.
Proof.
  intros i j input substring Hi Hj Hin Hsub Hprefix.
  apply (proj2 (list_eq_ext
    (sublist i (i + j) input)
    (sublist 0 j substring)
    0)).
  split.
  - rewrite !Zlength_sublist by lia. lia.
  - intros k Hk.
    rewrite Zlength_sublist in Hk by lia.
    rewrite !Znth_sublist by lia.
    replace (k + i) with (i + k) by lia.
    replace (k + 0) with k by lia.
    apply Hprefix.
    lia.
Qed.
Lemma mismatch_sublist_neq : forall i j input substring,
  0 <= i ->
  0 <= j ->
  i + j <= Zlength input ->
  j <= Zlength substring ->
  mismatch_prefix i j input substring ->
  sublist i (i + j) input <> sublist 0 j substring.
Proof.
  intros i j input substring Hi Hj Hin Hsub [k [Hk Hneq]] Heq.
  assert (Hklen : 0 <= k < Zlength (sublist i (i + j) input)).
  { rewrite Zlength_sublist by lia. lia. }
  pose proof (proj1 (list_eq_ext
    (sublist i (i + j) input)
    (sublist 0 j substring)
    0) Heq) as [_ Hnth_all].
  specialize (Hnth_all k Hklen) as Hnth.
  rewrite !Znth_sublist in Hnth by lia.
  replace (k + 0) with k in Hnth by lia.
  replace (k + i) with (i + k) in Hnth by lia.
  contradiction.
Qed.
Lemma match_progress_true_at_end : forall i input substring,
  0 <= i ->
  0 < Zlength substring ->
  i + Zlength substring <= Zlength input ->
  match_progress i (Zlength substring) 1 input substring ->
  match_at_zb i input substring = true.
Proof.
  intros i input substring Hi Hsub_pos Hin [Hprefix _].
  unfold match_at_zb.
  rewrite (proj2 (Z.ltb_lt 0 (Zlength substring))) by exact Hsub_pos.
  rewrite (proj2 (Z.leb_le (i + Zlength substring) (Zlength input))) by exact Hin.
  rewrite andb_true_r.
  apply list_eq_zb_true_iff.
  replace substring with (sublist 0 (Zlength substring) substring) at 2.
  - apply prefix_sublist_eq; try lia.
    apply Hprefix. reflexivity.
  - rewrite sublist_self by reflexivity.
    reflexivity.
Qed.
Lemma match_progress_false_at_end : forall i input substring,
  0 <= i ->
  0 < Zlength substring ->
  i + Zlength substring <= Zlength input ->
  match_progress i (Zlength substring) 0 input substring ->
  match_at_zb i input substring = false.
Proof.
  intros i input substring Hi Hsub_pos Hin [_ Hmis].
  unfold match_at_zb.
  rewrite (proj2 (Z.ltb_lt 0 (Zlength substring))) by exact Hsub_pos.
  rewrite (proj2 (Z.leb_le (i + Zlength substring) (Zlength input))) by exact Hin.
  rewrite andb_true_r.
  apply list_eq_zb_false_neq.
  replace substring with (sublist 0 (Zlength substring) substring) at 2.
  - apply mismatch_sublist_neq; try lia.
    apply Hmis. reflexivity.
  - rewrite sublist_self by reflexivity.
    reflexivity.
Qed.
Lemma match_at_zb_false_empty_substring : forall input substring i,
  Zlength substring = 0 ->
  match_at_zb i input substring = false.
Proof.
  intros input substring i Hlen.
  unfold match_at_zb.
  rewrite Hlen.
  reflexivity.
Qed.
Lemma match_at_zb_false_too_long : forall input substring i,
  Zlength input < Zlength substring ->
  0 <= i ->
  match_at_zb i input substring = false.
Proof.
  intros input substring i Hlt Hi.
  unfold match_at_zb.
  assert (Hgt : Zlength input < i + Zlength substring) by lia.
  pose proof (proj2 (Z.leb_gt (i + Zlength substring) (Zlength input)) Hgt) as Hleb.
  rewrite Hleb.
  destruct ((0 <? Zlength substring)%Z); reflexivity.
Qed.
Lemma match_at_zb_false_past_last : forall i input substring,
  0 < Zlength substring ->
  Zlength input - Zlength substring + 1 <= i ->
  match_at_zb i input substring = false.
Proof.
  intros i input substring Hpos Hi.
  unfold match_at_zb.
  rewrite (proj2 (Z.ltb_lt 0 (Zlength substring))) by exact Hpos.
  assert (Hgt : Zlength input < i + Zlength substring) by lia.
  rewrite (proj2 (Z.leb_gt (i + Zlength substring) (Zlength input)) Hgt).
  reflexivity.
Qed.
Lemma count_matches_upto_nat_all_false : forall fuel input substring,
  (forall idx, (idx < fuel)%nat ->
    match_at_zb (Z.of_nat idx) input substring = false) ->
  count_matches_upto_nat fuel input substring = 0.
Proof.
  induction fuel as [| fuel IH]; intros input substring Hfalse; simpl.
  - reflexivity.
  - rewrite IH.
    + rewrite Hfalse by lia. lia.
    + intros idx Hidx. apply Hfalse. lia.
Qed.
Lemma count_matches_upto_all_false : forall fuel input substring,
  0 <= fuel ->
  (forall idx, 0 <= idx < fuel ->
    match_at_zb idx input substring = false) ->
  count_matches_upto fuel input substring = 0.
Proof.
  intros fuel input substring Hfuel Hfalse.
  unfold count_matches_upto.
  apply count_matches_upto_nat_all_false.
  intros idx Hidx.
  apply Hfalse.
  lia.
Qed.
Lemma count_matches_upto_tail_false_nat : forall extra lo input substring,
  0 <= lo ->
  (forall idx, lo <= idx < lo + Z.of_nat extra ->
    match_at_zb idx input substring = false) ->
  count_matches_upto (lo + Z.of_nat extra) input substring =
  count_matches_upto lo input substring.
Proof.
  induction extra as [| extra IH]; intros lo input substring Hlo Hfalse.
  - replace (lo + Z.of_nat 0) with lo by lia. reflexivity.
  - replace (lo + Z.of_nat (S extra)) with (lo + Z.of_nat extra + 1) by lia.
    rewrite count_matches_upto_step_miss.
    + apply IH; [lia |].
      intros idx Hidx. apply Hfalse. lia.
    + lia.
    + apply Hfalse. lia.
Qed.
Lemma count_matches_upto_full_from_loop_bound : forall input substring,
  0 < Zlength substring ->
  Zlength substring <= Zlength input ->
  count_matches_upto (Zlength input) input substring =
  count_matches_upto (Zlength input - Zlength substring + 1) input substring.
Proof.
  intros input substring Hpos Hle.
  set (lo := Zlength input - Zlength substring + 1).
  replace (Zlength input) with (lo + (Zlength substring - 1)) by (subst lo; lia).
  rewrite <- (Z2Nat.id (Zlength substring - 1)) by lia.
  apply count_matches_upto_tail_false_nat.
  - subst lo. lia.
  - intros idx Hidx.
    apply match_at_zb_false_past_last; lia.
Qed.
Lemma problem_18_spec_count_matches_full : forall input substring,
  0 < Zlength substring ->
  Zlength substring <= Zlength input ->
  problem_18_spec input substring
    (count_matches_upto (Zlength input - Zlength substring + 1) input substring).
Proof.
  intros input substring Hpos Hle.
  unfold problem_18_spec.
  rewrite count_matches_upto_full_from_loop_bound by lia.
  reflexivity.
Qed.
Lemma problem_18_spec_zero_empty_substring : forall input substring,
  Zlength substring = 0 ->
  problem_18_spec input substring 0.
Proof.
  intros input substring Hlen.
  unfold problem_18_spec.
  rewrite count_matches_upto_all_false by
    (try apply Zlength_nonneg; intros idx _; apply match_at_zb_false_empty_substring; exact Hlen).
  reflexivity.
Qed.
Lemma problem_18_spec_zero_empty_input : forall input substring,
  Zlength input = 0 ->
  problem_18_spec input substring 0.
Proof.
  intros input substring Hlen.
  unfold problem_18_spec.
  rewrite Hlen.
  reflexivity.
Qed.
Lemma problem_18_spec_zero_too_long : forall input substring,
  Zlength input < Zlength substring ->
  problem_18_spec input substring 0.
Proof.
  intros input substring Hlt.
  unfold problem_18_spec.
  rewrite count_matches_upto_all_false by
    (try apply Zlength_nonneg; intros idx Hidx; apply match_at_zb_false_too_long; lia).
  reflexivity.
Qed.
Lemma count_matches_upto_zero_output : forall i input substring,
  i = 0 ->
  count_matches_upto i input substring = 0.
Proof. intros; subst; reflexivity. Qed.


Ltac c18_prep :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia.

Lemma proof_of_p018_how_many_times_safety_wit_26 : p018_how_many_times_safety_wit_26.
Proof.
  unfold p018_how_many_times_safety_wit_26.
  intros.
  c18_prep.
  pose proof (count_matches_upto_nonneg i l sub).
  pose proof (count_matches_upto_le i l sub ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_p018_how_many_times_entail_wit_1 : p018_how_many_times_entail_wit_1.
Proof.
  unfold p018_how_many_times_entail_wit_1.
  intros.
  c18_prep.
  entailer!.
Qed.

Lemma proof_of_p018_how_many_times_entail_wit_2 : p018_how_many_times_entail_wit_2.
Proof.
  unfold p018_how_many_times_entail_wit_2.
  intros.
  c18_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros1].
  entailer!.
  apply match_progress_init.
Qed.

Lemma proof_of_p018_how_many_times_entail_wit_3_1 : p018_how_many_times_entail_wit_3_1.
Proof.
  unfold p018_how_many_times_entail_wit_3_1.
  intros.
  c18_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2].
  entailer!.
  apply match_progress_step_new_mismatch; lia.
Qed.

Lemma proof_of_p018_how_many_times_entail_wit_3_2 : p018_how_many_times_entail_wit_3_2.
Proof.
  unfold p018_how_many_times_entail_wit_3_2.
  intros.
  c18_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2].
  entailer!.
  apply match_progress_step_keep_mismatch; assumption.
Qed.

Lemma proof_of_p018_how_many_times_entail_wit_3_3 : p018_how_many_times_entail_wit_3_3.
Proof.
  unfold p018_how_many_times_entail_wit_3_3.
  intros.
  c18_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros2].
  entailer!.
  apply match_progress_step_keep_mismatch; assumption.
Qed.

Lemma proof_of_p018_how_many_times_entail_wit_3_4 : p018_how_many_times_entail_wit_3_4.
Proof.
  unfold p018_how_many_times_entail_wit_3_4.
  intros.
  c18_prep.
  eapply derivable1_trans; [idtac | apply derivable1_orp_intros1].
  entailer!.
  apply match_progress_step_same; try assumption; lia.
Qed.

Lemma proof_of_p018_how_many_times_entail_wit_4_1 : p018_how_many_times_entail_wit_4_1.
Proof.
  unfold p018_how_many_times_entail_wit_4_1.
  intros.
  pre_process.
  assert (j = m) by lia.
  subst j.
  subst.
  repeat rewrite app_Znth1 in * by lia.
  assert (Hhit : match_at_zb i l sub = true).
  {
    apply match_progress_true_at_end; try lia.
    assumption.
  }
  rewrite count_matches_upto_step_hit by (try lia; exact Hhit).
  entailer!.
Qed.

Lemma proof_of_p018_how_many_times_entail_wit_4_2 : p018_how_many_times_entail_wit_4_2.
Proof.
  unfold p018_how_many_times_entail_wit_4_2.
  intros.
  pre_process.
  assert (j = m) by lia.
  subst j.
  subst.
  repeat rewrite app_Znth1 in * by lia.
  assert (Hmiss : match_at_zb i l sub = false).
  {
    apply match_progress_false_at_end; try lia.
    assumption.
  }
  rewrite count_matches_upto_step_miss by (try lia; exact Hmiss).
  entailer!.
Qed.

Lemma proof_of_p018_how_many_times_return_wit_1 : p018_how_many_times_return_wit_1.
Proof.
  unfold p018_how_many_times_return_wit_1.
  intros.
  c18_prep.
  assert (i = Zlength l - Zlength sub + 1) by lia.
  subst i.
  entailer!.
  apply problem_18_spec_count_matches_full; assumption || lia.
Qed. 

Lemma proof_of_p018_how_many_times_return_wit_2 : p018_how_many_times_return_wit_2.
Proof.
  unfold p018_how_many_times_return_wit_2.
  intros.
  c18_prep.
  entailer!.
  apply problem_18_spec_zero_too_long.
  lia.
Qed.

Lemma proof_of_p018_how_many_times_return_wit_3 : p018_how_many_times_return_wit_3.
Proof.
  unfold p018_how_many_times_return_wit_3.
  intros.
  c18_prep.
  entailer!.
  apply problem_18_spec_zero_empty_substring.
  lia.
Qed.

Lemma proof_of_p018_how_many_times_return_wit_4 : p018_how_many_times_return_wit_4.
Proof.
  unfold p018_how_many_times_return_wit_4.
  intros.
  c18_prep.
  entailer!.
  apply problem_18_spec_zero_empty_input.
  lia.
Qed.

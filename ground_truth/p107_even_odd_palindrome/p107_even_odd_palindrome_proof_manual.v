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
From SimpleC.EE.CAV.ground_truth_p107_even_odd_palindrome Require Import p107_even_odd_palindrome_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.

Import naive_C_Rules.
Require Import p107_even_odd_palindrome.
Local Open Scope sac.
From AUXLib Require Import ListLib.

Local Open Scope list_scope.

(* Proof helpers moved from p107_even_odd_palindrome.v so public contract files expose definitions only. *)

Lemma pal_reverse_loop_state_init : forall x,
  1 <= x <= 1000 ->
  pal_reverse_loop_state x x 0.
Proof.
  intros.
  unfold pal_reverse_loop_state.
  split.
  - lia.
  - exists 4%nat.
    repeat split; try lia.
Qed.
Lemma pal_reverse_loop_state_step : forall x t r,
  pal_reverse_loop_state x t r ->
  t > 0 ->
  pal_reverse_loop_state x (t / 10) (r * 10 + t mod 10).
Proof.
  intros x t r Hstate Ht.
  unfold pal_reverse_loop_state in *.
  destruct Hstate as [Hx [fuel [Ht_bounds [Hr_bounds [Hpow Heq]]]]].
  destruct fuel.
  {
    simpl in Hpow.
    lia.
  }
  simpl in Heq.
  assert ((t >? 0) = true) as Hgt by (apply Z.gtb_lt; lia).
  rewrite Hgt in Heq.
  split.
  - lia.
  - exists fuel.
    split.
    + split.
      * apply Z.div_pos; lia.
      * assert (t / 10 <= t) by (apply Z.div_le_upper_bound; lia).
        lia.
    + split.
      * destruct Hr_bounds as [[Hfuel Hr] | [[Hfuel Hr] | [[Hfuel Hr] | [[Hfuel Hr] | [Hfuel Hr]]]]];
          inversion Hfuel; subst; simpl in Hpow; try lia;
          assert (0 <= t mod 10 < 10) by (apply Z.mod_pos_bound; lia);
          try (left; split; lia);
          try (right; left; split; nia);
          try (right; right; left; split; nia);
          try (right; right; right; left; split; nia);
          try (right; right; right; right; split; nia).
      * split.
        -- assert (Hcur_lt: t < 10 * 10 ^ Z.of_nat fuel).
           {
             replace (10 ^ Z.of_nat (S fuel)) with (10 * 10 ^ Z.of_nat fuel) in Hpow.
             exact Hpow.
             rewrite Nat2Z.inj_succ.
             rewrite Z.pow_succ_r by lia.
             lia.
           }
           apply Z.div_lt_upper_bound.
           ++ lia.
           ++ nia.
        -- exact Heq.
Qed.
Lemma pal_reverse_loop_state_final : forall x r,
  pal_reverse_loop_state x 0 r ->
  r = reverse_digits_loop 4 x 0.
Proof.
  intros x r Hstate.
  unfold pal_reverse_loop_state in Hstate.
  destruct Hstate as [_ [fuel [[Ht_nonneg Ht_upper] [_ [_ Heq]]]]].
  destruct fuel.
  - simpl in Heq. exact Heq.
  - simpl in Heq. exact Heq.
Qed.
Lemma is_pal_model_correct_true : forall x,
  1 <= x <= 1000 ->
  reverse_digits_loop 4 x 0 = x ->
  is_pal_model x = 1.
Proof.
  intros.
  unfold is_pal_model, is_palindrome.
  assert (Z.leb x 0 = false) by (apply Z.leb_gt; lia).
  rewrite H1.
  assert ((reverse_digits_loop 4 x 0 =? x) = true) by (apply Z.eqb_eq; lia).
  rewrite H2.
  reflexivity.
Qed.
Lemma is_pal_model_correct_false : forall x,
  1 <= x <= 1000 ->
  reverse_digits_loop 4 x 0 <> x ->
  is_pal_model x = 0.
Proof.
  intros.
  unfold is_pal_model, is_palindrome.
  assert (Z.leb x 0 = false) by (apply Z.leb_gt; lia).
  rewrite H1.
  assert ((reverse_digits_loop 4 x 0 =? x) = false) by (apply Z.eqb_neq; lia).
  rewrite H2.
  reflexivity.
Qed.
Lemma count_even_pal_upto_step : forall k,
  0 <= k ->
  count_even_pal_upto (k + 1) =
    count_even_pal_upto k +
    (if andb (is_palindrome (k + 1)) (is_even (k + 1)) then 1 else 0).
Proof.
  intros.
  unfold count_even_pal_upto.
  replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  simpl.
  change (Z.pos (Pos.of_succ_nat (Z.to_nat k))) with (Z.of_nat (S (Z.to_nat k))).
  replace (Z.of_nat (S (Z.to_nat k))) with (k + 1) by lia.
  reflexivity.
Qed.
Lemma count_odd_pal_upto_step : forall k,
  0 <= k ->
  count_odd_pal_upto (k + 1) =
    count_odd_pal_upto k +
    (if andb (is_palindrome (k + 1)) (negb (is_even (k + 1))) then 1 else 0).
Proof.
  intros.
  unfold count_odd_pal_upto.
  replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  simpl.
  change (Z.pos (Pos.of_succ_nat (Z.to_nat k))) with (Z.of_nat (S (Z.to_nat k))).
  replace (Z.of_nat (S (Z.to_nat k))) with (k + 1) by lia.
  reflexivity.
Qed.
Lemma pal_count_prefix_init : forall n,
  1 <= n <= 1000 ->
  pal_count_prefix 0 n 0 0.
Proof.
  intros.
  unfold pal_count_prefix, count_even_pal_upto, count_odd_pal_upto.
  simpl.
  lia.
Qed.
Lemma pal_count_prefix_step_odd_hit : forall k n even_count odd_count,
  pal_count_prefix k n even_count odd_count ->
  0 <= k < n ->
  is_pal_model (k + 1) <> 0 ->
  (k + 1) mod 2 = 1 ->
  pal_count_prefix (k + 1) n even_count (odd_count + 1).
Proof.
  intros.
  unfold pal_count_prefix in *.
  destruct H as [Hbounds [Heven Hodd]].
  subst even_count odd_count.
  repeat split; try lia.
  - rewrite count_even_pal_upto_step by lia.
    assert (Hpal: is_palindrome (k + 1) = true).
    { unfold is_pal_model in H1. destruct (is_palindrome (k + 1)); lia. }
    assert (Hevenb: is_even (k + 1) = false).
    { unfold is_even. apply Z.eqb_neq. lia. }
    rewrite Hpal, Hevenb. simpl. lia.
  - rewrite count_odd_pal_upto_step by lia.
    assert (Hpal: is_palindrome (k + 1) = true).
    { unfold is_pal_model in H1. destruct (is_palindrome (k + 1)); lia. }
    assert (Hevenb: is_even (k + 1) = false).
    { unfold is_even. apply Z.eqb_neq. lia. }
    rewrite Hpal, Hevenb. simpl. lia.
Qed.
Lemma pal_count_prefix_step_even_hit : forall k n even_count odd_count,
  pal_count_prefix k n even_count odd_count ->
  0 <= k < n ->
  is_pal_model (k + 1) <> 0 ->
  (k + 1) mod 2 = 0 ->
  pal_count_prefix (k + 1) n (even_count + 1) odd_count.
Proof.
  intros.
  unfold pal_count_prefix in *.
  destruct H as [Hbounds [Heven Hodd]].
  subst even_count odd_count.
  repeat split; try lia.
  - rewrite count_even_pal_upto_step by lia.
    assert (Hpal: is_palindrome (k + 1) = true).
    { unfold is_pal_model in H1. destruct (is_palindrome (k + 1)); lia. }
    assert (Hevenb: is_even (k + 1) = true).
    { unfold is_even. apply Z.eqb_eq. lia. }
    rewrite Hpal, Hevenb. simpl. lia.
  - rewrite count_odd_pal_upto_step by lia.
    assert (Hpal: is_palindrome (k + 1) = true).
    { unfold is_pal_model in H1. destruct (is_palindrome (k + 1)); lia. }
    assert (Hevenb: is_even (k + 1) = true).
    { unfold is_even. apply Z.eqb_eq. lia. }
    rewrite Hpal, Hevenb. simpl. lia.
Qed.
Lemma pal_count_prefix_step_miss : forall k n even_count odd_count,
  pal_count_prefix k n even_count odd_count ->
  0 <= k < n ->
  is_pal_model (k + 1) = 0 ->
  pal_count_prefix (k + 1) n even_count odd_count.
Proof.
  intros.
  unfold pal_count_prefix in *.
  destruct H as [Hbounds [Heven Hodd]].
  subst even_count odd_count.
  repeat split; try lia.
  - rewrite count_even_pal_upto_step by lia.
    assert (Hpal: is_palindrome (k + 1) = false).
    { unfold is_pal_model in H1. destruct (is_palindrome (k + 1)); lia. }
    rewrite Hpal. simpl. lia.
  - rewrite count_odd_pal_upto_step by lia.
    assert (Hpal: is_palindrome (k + 1) = false).
    { unfold is_pal_model in H1. destruct (is_palindrome (k + 1)); lia. }
    rewrite Hpal. simpl. lia.
Qed.
Lemma count_even_pal_upto_nat_bounds : forall k,
  0 <= count_even_pal_upto_nat k <= Z.of_nat k.
Proof.
  induction k; simpl.
  - lia.
  - change (Z.pos (Pos.of_succ_nat k)) with (Z.of_nat (S k)).
    rewrite Nat2Z.inj_succ.
    destruct (andb (is_palindrome (Z.succ (Z.of_nat k)))
      (is_even (Z.succ (Z.of_nat k)))); lia.
Qed.
Lemma count_odd_pal_upto_nat_bounds : forall k,
  0 <= count_odd_pal_upto_nat k <= Z.of_nat k.
Proof.
  induction k; simpl.
  - lia.
  - change (Z.pos (Pos.of_succ_nat k)) with (Z.of_nat (S k)).
    rewrite Nat2Z.inj_succ.
    destruct (andb (is_palindrome (Z.succ (Z.of_nat k)))
      (negb (is_even (Z.succ (Z.of_nat k))))); lia.
Qed.
Lemma count_even_pal_upto_bounds : forall k,
  0 <= k ->
  0 <= count_even_pal_upto k <= k.
Proof.
  intros.
  unfold count_even_pal_upto.
  pose proof (count_even_pal_upto_nat_bounds (Z.to_nat k)).
  rewrite Z2Nat.id in H0 by lia.
  exact H0.
Qed.
Lemma count_odd_pal_upto_bounds : forall k,
  0 <= k ->
  0 <= count_odd_pal_upto k <= k.
Proof.
  intros.
  unfold count_odd_pal_upto.
  pose proof (count_odd_pal_upto_nat_bounds (Z.to_nat k)).
  rewrite Z2Nat.id in H0 by lia.
  exact H0.
Qed.
Lemma pal_count_prefix_bounds : forall k n even_count odd_count,
  pal_count_prefix k n even_count odd_count ->
  0 <= even_count <= k /\ 0 <= odd_count <= k.
Proof.
  intros.
  unfold pal_count_prefix in H.
  destruct H as [Hbounds [Heven Hodd]].
  subst.
  split.
  - apply count_even_pal_upto_bounds; lia.
  - apply count_odd_pal_upto_bounds; lia.
Qed.
Lemma problem_107_spec_of_prefix : forall n even_count odd_count,
  pal_count_prefix n n even_count odd_count ->
  problem_107_spec n [even_count; odd_count].
Proof.
  intros.
  unfold pal_count_prefix, problem_107_spec in *.
  destruct H as [_ [Heven Hodd]].
  subst.
  reflexivity.
Qed.


Lemma proof_of_is_pal_safety_wit_3 : is_pal_safety_wit_3.
Proof.
  pre_process.
  unfold pal_reverse_loop_state in H2.
  destruct H2 as [_ [fuel [[Ht_nonneg _] [Hr_bounds _]]]].
  assert (Hrem_bounds: 0 <= t % 10 < 10).
  { apply Z.rem_bound_pos; lia. }
  entailer!.
Qed.

Lemma proof_of_is_pal_safety_wit_5 : is_pal_safety_wit_5.
Proof.
  pre_process.
  unfold pal_reverse_loop_state in H2.
  destruct H2 as [_ [fuel [_ [Hr_bounds _]]]].
  entailer!.
Qed.

Lemma proof_of_is_pal_entail_wit_1 : is_pal_entail_wit_1.
Proof.
  pre_process.
  subst x_pre.
  entailer!.
  apply pal_reverse_loop_state_init.
  lia.
Qed.

Lemma proof_of_is_pal_entail_wit_2 : is_pal_entail_wit_2.
Proof.
  pre_process.
  assert (Ht_nonneg: 0 <= t)
    by (unfold pal_reverse_loop_state in H2;
        destruct H2 as [_ [fuel [[Ht_nonneg _] _]]]; lia).
  assert (t ÷ 10 = t / 10) as Hquot
    by (apply Z.quot_div_nonneg; lia).
  assert (t % 10 = t mod 10) as Hrem
    by (apply Z.rem_mod_nonneg; lia).
  rewrite Hquot, Hrem.
  entailer!.
  apply pal_reverse_loop_state_step; auto.
Qed.

Lemma proof_of_is_pal_return_wit_1 : is_pal_return_wit_1.
Proof.
  pre_process.
  assert (Ht0: t = 0)
    by (unfold pal_reverse_loop_state in H3;
        destruct H3 as [_ [fuel [[Ht_nonneg _] _]]]; lia).
  subst t.
  entailer!.
  symmetry.
  apply is_pal_model_correct_true; try lia.
  pose proof (pal_reverse_loop_state_final x0 r H3).
  lia.
Qed.

Lemma proof_of_is_pal_return_wit_2 : is_pal_return_wit_2.
Proof.
  pre_process.
  assert (Ht0: t = 0)
    by (unfold pal_reverse_loop_state in H3;
        destruct H3 as [_ [fuel [[Ht_nonneg _] _]]]; lia).
  subst t.
  entailer!.
  symmetry.
  apply is_pal_model_correct_false; try lia.
  intro Hrev.
  apply H.
  pose proof (pal_reverse_loop_state_final x0 r H3).
  lia.
Qed.

Lemma proof_of_p107_even_odd_palindrome_safety_wit_7 : p107_even_odd_palindrome_safety_wit_7.
Proof.
  pre_process.
  pose proof (pal_count_prefix_bounds _ _ _ _ H9).
  entailer!.
Qed.

Lemma proof_of_p107_even_odd_palindrome_safety_wit_23 : p107_even_odd_palindrome_safety_wit_23.
Proof.
  pre_process.
  pose proof (pal_count_prefix_bounds _ _ _ _ H12).
  entailer!.
Qed.

Lemma proof_of_p107_even_odd_palindrome_entail_wit_1 : p107_even_odd_palindrome_entail_wit_1.
Proof.
  pre_process.
  subst n_pre.
  entailer!.
  apply pal_count_prefix_init.
  lia.
Qed.

Lemma proof_of_p107_even_odd_palindrome_entail_wit_3_1 : p107_even_odd_palindrome_entail_wit_3_1.
Proof.
  pre_process.
  entailer!.
  replace (i + 1 - 1) with ((i - 1) + 1) by lia.
  eapply pal_count_prefix_step_even_hit with (k := i - 1); eauto; try lia.
  - replace (i - 1 + 1) with i by lia.
    rewrite <- H1. exact H0.
  - replace (i - 1 + 1) with i by lia.
    rewrite <- (Z.rem_mod_nonneg i 2) by lia.
    exact H.
Qed.

Lemma proof_of_p107_even_odd_palindrome_entail_wit_3_2 : p107_even_odd_palindrome_entail_wit_3_2.
Proof.
  pre_process.
  entailer!.
  replace (i + 1 - 1) with ((i - 1) + 1) by lia.
  eapply pal_count_prefix_step_miss with (k := i - 1); eauto; try lia.
  replace (i - 1 + 1) with i by lia.
  rewrite <- H2. exact H1.
Qed.

Lemma proof_of_p107_even_odd_palindrome_entail_wit_3_3 : p107_even_odd_palindrome_entail_wit_3_3.
Proof.
  pre_process.
  entailer!.
  assert (0 <= i % 2 < 2) by (apply Z.rem_bound_pos; lia).
  lia.
Qed.

Lemma proof_of_p107_even_odd_palindrome_entail_wit_3_4 : p107_even_odd_palindrome_entail_wit_3_4.
Proof.
  pre_process.
  entailer!.
  replace (i + 1 - 1) with ((i - 1) + 1) by lia.
  eapply pal_count_prefix_step_odd_hit with (k := i - 1); eauto; try lia.
  - replace (i - 1 + 1) with i by lia.
    rewrite <- H4. exact H3.
  - replace (i - 1 + 1) with i by lia.
    rewrite <- (Z.rem_mod_nonneg i 2) by lia.
    exact H2.
Qed.

Lemma proof_of_p107_even_odd_palindrome_return_wit_1 : p107_even_odd_palindrome_return_wit_1.
Proof.
  pre_process.
  Exists (num2 :: num1 :: nil) 2 retval.
  unfold IntArray.full, store_array.
  simpl.
  entailer!.
  eapply problem_107_spec_of_prefix.
  assert (i - 1 = n0) by lia.
  rewrite H8 in H7.
  exact H7.
Qed.

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
From SimpleC.EE.CAV.ground_truth_p033_sort_third Require Import p033_sort_third_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Arith.PeanoNat.
Require Import Lia.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p033_sort_third.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p033_sort_third.v so public contract files expose definitions only. *)

Lemma third_count_0 :
  third_count 0 = 0.
Proof.
  unfold third_count.
  reflexivity.
Qed.
Lemma third_count_nonneg_le : forall n,
  0 <= n ->
  0 <= third_count n <= n.
Proof.
  intros n Hn.
  unfold third_count.
  destruct (Zquot.Zquotrem_Zdiv_eucl_pos (n + 2) 3) as [Hq _]; try lia.
  rewrite Hq.
  split.
  - apply Z.div_pos; lia.
  - destruct (Z.eq_dec n 0) as [-> | Hnz].
    + cbn. lia.
    + apply Z.div_le_upper_bound; lia.
Qed.
Lemma third_count_after_hit : forall n i,
  0 <= n ->
  0 <= i ->
  i * 3 < n ->
  i + 1 <= third_count n.
Proof.
  intros n i Hn Hi Hlt.
  unfold third_count.
  destruct (Zquot.Zquotrem_Zdiv_eucl_pos (n + 2) 3) as [Hq _]; try lia.
  rewrite Hq.
  apply Z.div_le_lower_bound; lia.
Qed.
Lemma third_count_exit_index : forall n i,
  0 <= n ->
  0 <= i ->
  i <= third_count n ->
  i * 3 >= n ->
  i = third_count n.
Proof.
  intros n i Hn Hi Hle Hge.
  unfold third_count in *.
  destruct (Zquot.Zquotrem_Zdiv_eucl_pos (n + 2) 3) as [Hq _]; try lia.
  rewrite Hq in *.
  apply Z.le_antisymm; [assumption |].
  apply Z.lt_succ_r.
  apply Z.div_lt_upper_bound; lia.
Qed.
Lemma third_count_step_mod0 : forall i,
  0 <= i ->
  Z.rem i 3 = 0 ->
  third_count (i + 1) = third_count i + 1.
Proof.
  intros i Hi Hrem.
  unfold third_count.
  destruct (Zquot.Zquotrem_Zdiv_eucl_pos i 3) as [Hqi Hri]; try lia.
  destruct (Zquot.Zquotrem_Zdiv_eucl_pos (i + 3) 3) as [Hq3 _]; try lia.
  destruct (Zquot.Zquotrem_Zdiv_eucl_pos (i + 2) 3) as [Hq2 _]; try lia.
  replace (i + 1 + 2) with (i + 3) by lia.
  rewrite Hq3, Hq2.
  assert (Hmod : i mod 3 = 0) by congruence.
  pose proof (Z.div_mod i 3 ltac:(lia)) as Hdm.
  rewrite Hmod in Hdm.
  replace (i + 3) with ((i / 3 + 1) * 3 + 0) by lia.
  replace (i + 2) with ((i / 3) * 3 + 2) by lia.
  rewrite Z.div_add_l by lia.
  rewrite Z.div_add_l by lia.
  change (0 / 3) with 0.
  change (2 / 3) with 0.
  lia.
Qed.
Lemma third_count_mod0_quot : forall i,
  0 <= i ->
  Z.rem i 3 = 0 ->
  third_count i = i ÷ 3.
Proof.
  intros i Hi Hrem.
  unfold third_count.
  destruct (Zquot.Zquotrem_Zdiv_eucl_pos i 3) as [Hqi Hri]; try lia.
  destruct (Zquot.Zquotrem_Zdiv_eucl_pos (i + 2) 3) as [Hq2 _]; try lia.
  rewrite Hqi, Hq2.
  assert (Hmod : i mod 3 = 0) by congruence.
  pose proof (Z.div_mod i 3 ltac:(lia)) as Hdm.
  rewrite Hmod in Hdm.
  replace (i + 2) with ((i / 3) * 3 + 2) by lia.
  rewrite Z.div_add_l by lia.
  change (2 / 3) with 0.
  lia.
Qed.
Lemma third_count_step_not_mod0 : forall i,
  0 <= i ->
  Z.rem i 3 <> 0 ->
  third_count (i + 1) = third_count i.
Proof.
  intros i Hi Hrem.
  unfold third_count.
  destruct (Zquot.Zquotrem_Zdiv_eucl_pos i 3) as [Hq Hm]; try lia.
  destruct (Zquot.Zquotrem_Zdiv_eucl_pos (i + 2) 3) as [Hq2 _]; try lia.
  destruct (Zquot.Zquotrem_Zdiv_eucl_pos (i + 3) 3) as [Hq3 _]; try lia.
  replace (i + 1 + 2) with (i + 3) by lia.
  rewrite Hq2, Hq3.
  assert (0 <= i mod 3 < 3) by (apply Z.mod_pos_bound; lia).
  assert (i mod 3 <> 0) by congruence.
  assert (i mod 3 = 1 \/ i mod 3 = 2) by lia.
  destruct H1 as [Hr | Hr].
  - replace (i + 2) with ((i / 3 + 1) * 3 + 0) by
      (pose proof (Z.div_mod i 3 ltac:(lia)); lia).
    replace (i + 3) with ((i / 3 + 1) * 3 + 1) by
      (pose proof (Z.div_mod i 3 ltac:(lia)); lia).
    rewrite Z.div_add_l by lia.
    rewrite Z.div_add_l by lia.
    change (0 / 3) with 0.
    change (1 / 3) with 0.
    lia.
  - replace (i + 2) with ((i / 3 + 1) * 3 + 1) by
      (pose proof (Z.div_mod i 3 ltac:(lia)); lia).
    replace (i + 3) with ((i / 3 + 1) * 3 + 2) by
      (pose proof (Z.div_mod i 3 ltac:(lia)); lia).
    rewrite Z.div_add_l by lia.
    rewrite Z.div_add_l by lia.
    change (1 / 3) with 0.
    change (2 / 3) with 0.
    lia.
Qed.
Lemma third_values_prefix_Zlength : forall n input,
  0 <= n ->
  Zlength (third_values_prefix n input) = n.
Proof.
  intros n input Hn.
  unfold third_values_prefix.
  rewrite Zlength_correct.
  replace n with (Z.of_nat (Z.to_nat n)) at 2 by lia.
  revert input.
  induction (Z.to_nat n); intros; simpl; [reflexivity |].
  rewrite app_length.
  simpl.
  rewrite Nat2Z.inj_add.
  simpl.
  rewrite IHn0.
  lia.
Qed.
Lemma third_values_prefix_0 : forall input,
  third_values_prefix 0 input = nil.
Proof.
  reflexivity.
Qed.
Lemma third_values_prefix_snoc : forall i input,
  0 <= i ->
  third_values_prefix (i + 1) input =
  third_values_prefix i input ++ [Znth (3 * i) input 0].
Proof.
  intros i input Hi.
  unfold third_values_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.
Lemma sort_third_output_prefix_Zlength : forall n input sorted_third,
  0 <= n ->
  Zlength (sort_third_output_prefix n input sorted_third) = n.
Proof.
  intros n input sorted_third Hn.
  unfold sort_third_output_prefix.
  rewrite Zlength_correct.
  replace n with (Z.of_nat (Z.to_nat n)) at 2 by lia.
  revert input sorted_third.
  induction (Z.to_nat n); intros; simpl; [reflexivity |].
  rewrite app_length.
  simpl.
  rewrite Nat2Z.inj_add.
  simpl.
  rewrite IHn0.
  lia.
Qed.
Lemma sort_third_output_prefix_0 : forall input sorted_third,
  sort_third_output_prefix 0 input sorted_third = nil.
Proof.
  reflexivity.
Qed.
Lemma sort_third_output_prefix_snoc : forall i input sorted_third,
  0 <= i ->
  sort_third_output_prefix (i + 1) input sorted_third =
  sort_third_output_prefix i input sorted_third ++
    [choose_sort_third_value i input sorted_third].
Proof.
  intros i input sorted_third Hi.
  unfold sort_third_output_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.
Lemma choose_sort_third_value_mod0 : forall i input sorted_third,
  Z.rem i 3 = 0 ->
  choose_sort_third_value i input sorted_third = Znth (i ÷ 3) sorted_third 0.
Proof.
  intros.
  unfold choose_sort_third_value.
  rewrite H.
  reflexivity.
Qed.
Lemma choose_sort_third_value_not_mod0 : forall i input sorted_third,
  Z.rem i 3 <> 0 ->
  choose_sort_third_value i input sorted_third = Znth i input 0.
Proof.
  intros.
  unfold choose_sort_third_value.
  destruct (Z.eqb_spec (Z.rem i 3) 0); congruence.
Qed.
Lemma sorted_int_list_by_1 : forall l,
  sorted_int_list_by 1 l ->
  sorted_ascending l.
Proof.
  intros l H.
  exact H.
Qed.
Lemma sort_third_output_Zlength : forall input sorted_third,
  Zlength (sort_third_output input sorted_third) = Zlength input.
Proof.
  intros.
  unfold sort_third_output.
  apply sort_third_output_prefix_Zlength.
  apply Zlength_nonneg.
Qed.
Lemma nonthird_values_prefix_snoc : forall i input,
  0 <= i ->
  nonthird_values_prefix (i + 1) input =
  nonthird_values_prefix i input ++
    if Z.eqb (Z.rem i 3) 0 then nil else [Znth i input 0].
Proof.
  intros i input Hi.
  unfold nonthird_values_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.
Lemma sublist_snoc_Znth_33 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0].
Proof.
  intros.
  rewrite (@sublist_split Z 0 (i + 1) i l) by (destruct H; lia).
  rewrite (@sublist_single Z 0 i l) by (destruct H; lia).
  reflexivity.
Qed.
Lemma sublist_snoc_last_33 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0].
Proof.
  apply sublist_snoc_Znth_33.
Qed.
Lemma count_occ_app_single : forall l x y,
  count_occ Z.eq_dec (l ++ [y]) x =
  (count_occ Z.eq_dec l x + if Z.eq_dec y x then 1 else 0)%nat.
Proof.
  intros.
  rewrite count_occ_app.
  simpl.
  lia.
Qed.
Lemma count_occ_app_nil : forall l x,
  count_occ Z.eq_dec (l ++ nil) x = count_occ Z.eq_dec l x.
Proof.
  intros.
  rewrite app_nil_r.
  reflexivity.
Qed.
Lemma count_occ_third_values_prefix_step : forall i input x,
  0 <= i ->
  Z.rem i 3 = 0 ->
  count_occ Z.eq_dec (third_values_prefix (third_count (i + 1)) input) x =
  (count_occ Z.eq_dec (third_values_prefix (third_count i) input) x +
  (if Z.eq_dec (Znth i input 0%Z) x then 1 else 0))%nat.
Proof.
  intros i input x Hi Hrem.
  rewrite third_count_step_mod0 by lia.
  rewrite third_values_prefix_snoc by (pose proof (third_count_nonneg_le i Hi); lia).
  rewrite count_occ_app_single.
  rewrite third_count_mod0_quot by lia.
  replace (3 * (i ÷ 3)) with i.
  - reflexivity.
  - pose proof (Z.quot_rem i 3 ltac:(lia)).
    lia.
Qed.
Lemma count_occ_third_values_prefix_not_step : forall i input x,
  0 <= i ->
  Z.rem i 3 <> 0 ->
  count_occ Z.eq_dec (third_values_prefix (third_count (i + 1)) input) x =
  count_occ Z.eq_dec (third_values_prefix (third_count i) input) x.
Proof.
  intros.
  rewrite third_count_step_not_mod0 by lia.
  reflexivity.
Qed.
Lemma count_occ_nonthird_values_prefix_step_mod0 : forall i input x,
  0 <= i ->
  Z.rem i 3 = 0 ->
  count_occ Z.eq_dec (nonthird_values_prefix (i + 1) input) x =
  count_occ Z.eq_dec (nonthird_values_prefix i input) x.
Proof.
  intros.
  rewrite nonthird_values_prefix_snoc by lia.
  destruct (Z.eqb_spec (Z.rem i 3) 0); [ | congruence].
  rewrite app_nil_r.
  reflexivity.
Qed.
Lemma count_occ_nonthird_values_prefix_step_not : forall i input x,
  0 <= i ->
  Z.rem i 3 <> 0 ->
  count_occ Z.eq_dec (nonthird_values_prefix (i + 1) input) x =
  (count_occ Z.eq_dec (nonthird_values_prefix i input) x +
  (if Z.eq_dec (Znth i input 0%Z) x then 1 else 0))%nat.
Proof.
  intros.
  rewrite nonthird_values_prefix_snoc by lia.
  destruct (Z.eqb_spec (Z.rem i 3) 0); [congruence |].
  rewrite count_occ_app_single.
  reflexivity.
Qed.
Lemma count_occ_sublist_decomp : forall n input x,
  0 <= n <= Zlength input ->
  count_occ Z.eq_dec (sublist 0 n input) x =
  (count_occ Z.eq_dec (third_values_prefix (third_count n) input) x +
  count_occ Z.eq_dec (nonthird_values_prefix n input) x)%nat.
Proof.
  intros n input x Hn.
  assert (Hnat : n = Z.of_nat (Z.to_nat n)) by lia.
  rewrite Hnat in Hn |- *.
  remember (Z.to_nat n) as m eqn:Hm.
  clear Hnat n Hm.
  induction m as [|m IH].
  - unfold sublist, third_values_prefix, nonthird_values_prefix, third_count.
    simpl.
    reflexivity.
  - rewrite Nat2Z.inj_succ in *.
    replace (Z.succ (Z.of_nat m)) with (Z.of_nat m + 1) in * by lia.
    rewrite sublist_snoc_Znth_33 by lia.
    rewrite count_occ_app_single.
    rewrite IH by lia.
    destruct (Z.eq_dec (Z.rem (Z.of_nat m) 3) 0) as [Hrem | Hrem].
    + rewrite count_occ_third_values_prefix_step by lia.
      rewrite count_occ_nonthird_values_prefix_step_mod0 by lia.
      lia.
    + rewrite count_occ_third_values_prefix_not_step by lia.
      rewrite count_occ_nonthird_values_prefix_step_not by lia.
      lia.
Qed.
Lemma count_occ_sort_output_prefix_decomp : forall n input sorted_third x,
  0 <= n ->
  third_count n <= Zlength sorted_third ->
  count_occ Z.eq_dec (sort_third_output_prefix n input sorted_third) x =
  (count_occ Z.eq_dec (sublist 0 (third_count n) sorted_third) x +
  count_occ Z.eq_dec (nonthird_values_prefix n input) x)%nat.
Proof.
  intros n input sorted_third x Hn Hlen.
  assert (Hnat : n = Z.of_nat (Z.to_nat n)) by lia.
  rewrite Hnat in Hn, Hlen |- *.
  remember (Z.to_nat n) as m eqn:Hm.
  clear Hnat n Hm.
  induction m as [|m IH].
  - unfold sort_third_output_prefix, nonthird_values_prefix, third_count, sublist.
    simpl.
    reflexivity.
  - rewrite Nat2Z.inj_succ in *.
    replace (Z.succ (Z.of_nat m)) with (Z.of_nat m + 1) in * by lia.
    rewrite sort_third_output_prefix_snoc by lia.
    rewrite count_occ_app_single.
    destruct (Z.eq_dec (Z.rem (Z.of_nat m) 3) 0) as [Hrem | Hrem].
    + rewrite choose_sort_third_value_mod0 by lia.
      rewrite third_count_step_mod0 in Hlen |- * by lia.
      rewrite sublist_snoc_last_33 by
        (pose proof (third_count_nonneg_le (Z.of_nat m) ltac:(lia)); lia).
      rewrite count_occ_app_single.
      rewrite IH by lia.
      rewrite count_occ_nonthird_values_prefix_step_mod0 by lia.
      rewrite third_count_mod0_quot by lia.
      lia.
    + rewrite choose_sort_third_value_not_mod0 by lia.
      rewrite third_count_step_not_mod0 in Hlen |- * by lia.
      rewrite count_occ_nonthird_values_prefix_step_not by lia.
      rewrite IH by lia.
      lia.
Qed.
Lemma sort_third_output_prefix_Znth : forall n input sorted_third i,
  0 <= i < n ->
  Znth i (sort_third_output_prefix n input sorted_third) 0 =
  choose_sort_third_value i input sorted_third.
Proof.
  intros n input sorted_third i Hrange.
  assert (Hnat : n = Z.of_nat (Z.to_nat n)) by lia.
  rewrite Hnat in Hrange |- *.
  remember (Z.to_nat n) as m eqn:Hm.
  clear Hnat n Hm.
  revert i Hrange.
  induction m as [|m IH]; intros i Hrange; [lia |].
  rewrite Nat2Z.inj_succ in *.
  replace (Z.succ (Z.of_nat m)) with (Z.of_nat m + 1) in * by lia.
  rewrite sort_third_output_prefix_snoc by lia.
  destruct (Z.eq_dec i (Z.of_nat m)) as [-> | Hneq].
  - rewrite app_Znth2.
    + rewrite sort_third_output_prefix_Zlength by lia.
      replace (Z.of_nat m - Z.of_nat m) with 0 by lia.
      apply Znth0_cons.
    + rewrite sort_third_output_prefix_Zlength by lia.
      lia.
  - rewrite app_Znth1.
    + apply IH; lia.
    + rewrite sort_third_output_prefix_Zlength by lia.
      lia.
Qed.
Lemma sort_third_output_prefix_nth_not_mod0 : forall input sorted_third i,
  0 <= i < Zlength input ->
  Z.rem i 3 <> 0 ->
  Znth i (sort_third_output input sorted_third) 0 = Znth i input 0.
Proof.
  intros.
  unfold sort_third_output.
  rewrite sort_third_output_prefix_Znth by lia.
  apply choose_sort_third_value_not_mod0.
  assumption.
Qed.
Lemma sort_third_output_prefix_nth_mod0 : forall input sorted_third i,
  0 <= i < Zlength input ->
  Z.rem i 3 = 0 ->
  Znth i (sort_third_output input sorted_third) 0 =
  Znth (i ÷ 3) sorted_third 0.
Proof.
  intros.
  unfold sort_third_output.
  rewrite sort_third_output_prefix_Znth by lia.
  apply choose_sort_third_value_mod0.
  assumption.
Qed.
Lemma nat_mod3_to_Zrem : forall i,
  (i mod 3 = 0)%nat ->
  Z.rem (Z.of_nat i) 3 = 0.
Proof.
  intros i H.
  destruct (Zquot.Zquotrem_Zdiv_eucl_pos (Z.of_nat i) 3) as [_ Hr]; try lia.
  rewrite Hr.
  replace 3 with (Z.of_nat 3) by reflexivity.
  rewrite <- Nat2Z.inj_mod by lia.
  rewrite H.
  reflexivity.
Qed.
Lemma nat_not_mod3_to_Zrem : forall i,
  (i mod 3 <> 0)%nat ->
  Z.rem (Z.of_nat i) 3 <> 0.
Proof.
  intros i H Hrem.
  apply H.
  destruct (Zquot.Zquotrem_Zdiv_eucl_pos (Z.of_nat i) 3) as [_ Hr]; try lia.
  rewrite Hr in Hrem.
  apply Nat2Z.inj.
  replace 3 with (Z.of_nat 3) in Hrem by reflexivity.
  rewrite Nat2Z.inj_mod by lia.
  exact Hrem.
Qed.
Lemma nat_mod0_div3_quot : forall i,
  (i mod 3 = 0)%nat ->
  Z.of_nat (i / 3) = Z.of_nat i ÷ 3.
Proof.
  intros i Hmod.
  destruct (Zquot.Zquotrem_Zdiv_eucl_pos (Z.of_nat i) 3) as [Hq Hr]; try lia.
  rewrite Hq.
  replace 3 with (Z.of_nat 3) by reflexivity.
  rewrite <- Nat2Z.inj_div by lia.
  reflexivity.
Qed.
Lemma sort_third_output_problem_33_spec : forall input sorted_third,
  Zlength sorted_third = third_count (Zlength input) ->
  sorted_int_list_by 1 sorted_third ->
  Permutation (third_values_prefix (third_count (Zlength input)) input) sorted_third ->
  problem_33_spec input (sort_third_output input sorted_third).
Proof.
  intros input sorted_third Hlen Hsorted Hperm.
  unfold problem_33_spec, problem_33_spec.
  repeat split.
  - apply (Permutation_count_occ Z.eq_dec).
    intros x.
    rewrite <- (sublist_self input (Zlength input)) at 1 by lia.
    rewrite count_occ_sublist_decomp by (pose proof (Zlength_nonneg input); lia).
    unfold sort_third_output.
    rewrite count_occ_sort_output_prefix_decomp.
    + rewrite (sublist_self sorted_third (third_count (Zlength input))) by lia.
      pose proof (proj1 (Permutation_count_occ Z.eq_dec _ _) Hperm x) as Hcnt.
      lia.
    + apply Zlength_nonneg.
    + lia.
  - intros i Hi Hmod.
    apply sort_third_output_prefix_nth_not_mod0; assumption.
  - intros i j Hcond.
    destruct Hcond as [Hi [Hj [Himod [Hjmod Hij]]]].
    assert (Hi_input : 0 <= i < Zlength input) by
      (rewrite <- (sort_third_output_Zlength input sorted_third); exact Hi).
    assert (Hj_input : 0 <= j < Zlength input) by
      (rewrite <- (sort_third_output_Zlength input sorted_third); exact Hj).
    pose proof (sort_third_output_prefix_nth_mod0
      input sorted_third i Hi_input Himod) as Hzi.
    pose proof (sort_third_output_prefix_nth_mod0
      input sorted_third j Hj_input Hjmod) as Hzj.
    rewrite Hzi.
    rewrite Hzj.
    apply sorted_int_list_by_1 in Hsorted.
    apply Hsorted.
    + pose proof (Z.quot_rem i 3 ltac:(lia)) as Hqi.
      pose proof (Z.quot_rem j 3 ltac:(lia)) as Hqj.
      rewrite Himod in Hqi.
      rewrite Hjmod in Hqj.
      lia.
    + rewrite Hlen.
      pose proof (Z.quot_rem j 3 ltac:(lia)) as Hqj.
      rewrite Hjmod in Hqj.
      assert (Hhit : (j ÷ 3) * 3 < Zlength input) by lia.
      pose proof (third_count_after_hit (Zlength input) (j ÷ 3)
        (Zlength_nonneg input) ltac:(lia) Hhit).
      lia.
Qed.


Lemma proof_of_p033_sort_third_entail_wit_1 : p033_sort_third_entail_wit_1.
Proof.
  pre_process.
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
  - pose proof (third_count_nonneg_le l_size_pre ltac:(lia)) as [_ Hle].
    unfold third_count in Hle.
    exact Hle.
  - pose proof (third_count_nonneg_le l_size_pre ltac:(lia)) as [Hge _].
    unfold third_count in Hge.
    exact Hge.
  - pose proof (third_count_nonneg_le l_size_pre ltac:(lia)) as [Hge _].
    unfold third_count in Hge.
    exact Hge.
Qed. 

Lemma proof_of_p033_sort_third_entail_wit_2 : p033_sort_third_entail_wit_2.
Proof.
  pre_process.
  rewrite third_values_prefix_snoc by lia.
  replace (i * 3) with (3 * i) in * by lia.
  entailer!.
  - rewrite Zlength_app.
    rewrite Zlength_cons, Zlength_nil.
    rewrite <- H13.
    lia.
  - subst third_size.
    apply third_count_after_hit; lia.
Qed. 

Lemma proof_of_p033_sort_third_entail_wit_3 : p033_sort_third_entail_wit_3.
Proof.
  pre_process.
  assert (Hi : i = third_size).
  {
    subst third_size.
    apply third_count_exit_index; lia.
  }
  subst i.
  entailer!.
Qed. 

Lemma proof_of_p033_sort_third_entail_wit_5 : p033_sort_third_entail_wit_5.
Proof.
  pre_process.
  Exists sorted_full_l_2 sorted_third_l_2.
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
Qed. 

Lemma proof_of_p033_sort_third_entail_wit_6_1 : p033_sort_third_entail_wit_6_1.
Proof.
  pre_process.
  Exists sorted_full_l_2 sorted_third_l_2.
  assert (Hjquot : j = i ÷ 3).
  {
    subst j.
    apply third_count_mod0_quot; lia.
  }
  assert (Hjlt : j < third_size).
  {
    subst third_size j.
    rewrite third_count_mod0_quot by lia.
    assert (Hhit : (i ÷ 3) * 3 < l_size_pre).
    {
      pose proof (Z.quot_rem i 3 ltac:(lia)).
      lia.
    }
    pose proof (third_count_after_hit l_size_pre (i ÷ 3) ltac:(lia) ltac:(lia) Hhit).
    lia.
  }
  assert (Hz : Znth j sorted_full_l_2 0 = Znth j sorted_third_l_2 0).
  {
    rewrite <- H10.
    rewrite Znth_sublist by lia.
    replace (j + 0) with j by lia.
    reflexivity.
  }
  rewrite sort_third_output_prefix_snoc by lia.
  rewrite choose_sort_third_value_mod0 by lia.
  rewrite <- Hjquot.
  rewrite Hz.
  entailer!.
  - subst j.
    rewrite third_count_step_mod0 by lia.
    lia.
Qed. 

Lemma proof_of_p033_sort_third_entail_wit_6_2 : p033_sort_third_entail_wit_6_2.
Proof.
  pre_process.
  Exists sorted_full_l_2 sorted_third_l_2.
  rewrite sort_third_output_prefix_snoc by lia.
  rewrite choose_sort_third_value_not_mod0 by lia.
  entailer!.
  - subst j.
    rewrite third_count_step_not_mod0 by lia.
    reflexivity.
Qed. 

Lemma proof_of_p033_sort_third_return_wit_1 : p033_sort_third_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = l_size_pre) by lia.
  subst i.
  Exists (sort_third_output_prefix l_size_pre input_l sorted_third_l) l_size_pre data_2.
  sep_apply (IntArray.seg_to_full data_2 0 l_size_pre).
  replace (data_2 + 0 * sizeof (INT)) with data_2 by lia.
  replace (l_size_pre - 0) with l_size_pre by lia.
  entailer!.
  - rewrite H5.
    fold (sort_third_output input_l sorted_third_l).
    subst third_size.
    rewrite H5 in H7, H11.
    apply sort_third_output_problem_33_spec.
    + symmetry; assumption.
    + assumption.
    + assumption.
  - rewrite sort_third_output_prefix_Zlength by lia.
    lia.
Qed.

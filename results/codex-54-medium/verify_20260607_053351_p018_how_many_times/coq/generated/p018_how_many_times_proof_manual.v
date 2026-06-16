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
From SimpleC.EE.CAV.verify_20260607_053351_p018_how_many_times Require Import p018_how_many_times_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p018_how_many_times.
Local Open Scope sac.

Lemma proof_of_p018_how_many_times_safety_wit_29 : p018_how_many_times_safety_wit_29.
Proof.
  pre_process.
  prop_apply (store_int_range (&("n0")) n).
  Intros.
  change Int.min_signed with (-2147483648) in H10.
  change Int.max_signed with (2147483647) in H10.
  entailer!.
  - assert (Hcount_bounds: 0 <= count_matches_upto i l sub <= i).
    {
      assert (Hnat_bounds: forall fuel,
        0 <= count_matches_upto_nat fuel l sub <= Z.of_nat fuel).
      {
        induction fuel; simpl.
        - lia.
        - destruct (match_at_zb (Z.of_nat fuel) l sub); lia.
      }
      unfold count_matches_upto.
      specialize (Hnat_bounds (Z.to_nat i)).
      rewrite Z2Nat.id in Hnat_bounds by lia.
      lia.
    }
    destruct Hcount_bounds as [Hcount_nonneg _].
    rewrite H7.
    lia.
  - assert (Hcount_bounds: 0 <= count_matches_upto i l sub <= i).
    {
      assert (Hnat_bounds: forall fuel,
        0 <= count_matches_upto_nat fuel l sub <= Z.of_nat fuel).
      {
        induction fuel; simpl.
        - lia.
        - destruct (match_at_zb (Z.of_nat fuel) l sub); lia.
      }
      unfold count_matches_upto.
      specialize (Hnat_bounds (Z.to_nat i)).
      rewrite Z2Nat.id in Hnat_bounds by lia.
      lia.
    }
    destruct Hcount_bounds as [_ Hcount_upper].
    rewrite H7.
    lia.
Qed.

Lemma proof_of_p018_how_many_times_entail_wit_1 : p018_how_many_times_entail_wit_1.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  subst retval retval_2.
  split_pure_spatial.
  - cancel (CharArray.full substring_pre (m + 1) (sub ++ 0 :: nil)).
    cancel (CharArray.full str_pre (n + 1) (l ++ 0 :: nil)).
    cancel ((&("m0")) # Int |-> m).
    cancel ((&("n0")) # Int |-> n).
  - entailer!.
Qed.

Lemma proof_of_p018_how_many_times_entail_wit_2_1 : p018_how_many_times_entail_wit_2_1.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  unfold match_progress, match_prefix, mismatch_prefix.
  entailer!.
Qed.

Lemma proof_of_p018_how_many_times_entail_wit_2_2 : p018_how_many_times_entail_wit_2_2.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  unfold match_progress, match_prefix, mismatch_prefix.
  entailer!.
Qed.

Lemma proof_of_p018_how_many_times_entail_wit_3_1 : p018_how_many_times_entail_wit_3_1.
Proof.
  pre_process.
  prop_apply (CharArray.full_Zlength substring_pre (m + 1) (sub ++ 0 :: nil)).
  Intros.
  prop_apply (CharArray.full_Zlength str_pre (n + 1) (l ++ 0 :: nil)).
  Intros.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in H12, H13.
  rewrite app_Znth1 in H by lia.
  rewrite app_Znth1 in H by lia.
  rewrite <- derivable1_orp_intros1.
  unfold match_progress, match_prefix, mismatch_prefix in *.
  split_pure_spatial.
  - cancel (CharArray.full str_pre (n + 1) (l ++ 0 :: nil)).
    cancel (CharArray.full substring_pre (m + 1) (sub ++ 0 :: nil)).
  - entailer!.
    intros _. exists j. lia.
Qed.

Lemma proof_of_p018_how_many_times_entail_wit_3_2 : p018_how_many_times_entail_wit_3_2.
Proof.
  pre_process.
  prop_apply (CharArray.full_Zlength substring_pre (m + 1) (sub ++ 0 :: nil)).
  Intros.
  prop_apply (CharArray.full_Zlength str_pre (n + 1) (l ++ 0 :: nil)).
  Intros.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in H12, H13.
  rewrite app_Znth1 in H by lia.
  rewrite app_Znth1 in H by lia.
  rewrite <- derivable1_orp_intros1.
  unfold match_progress, match_prefix, mismatch_prefix in *.
  split_pure_spatial.
  - cancel (CharArray.full str_pre (n + 1) (l ++ 0 :: nil)).
    cancel (CharArray.full substring_pre (m + 1) (sub ++ 0 :: nil)).
  - entailer!.
    intros _. exists j. lia.
Qed.

Lemma proof_of_p018_how_many_times_entail_wit_3_3 : p018_how_many_times_entail_wit_3_3.
Proof.
  pre_process.
  prop_apply (CharArray.full_Zlength substring_pre (m + 1) (sub ++ 0 :: nil)).
  Intros.
  prop_apply (CharArray.full_Zlength str_pre (n + 1) (l ++ 0 :: nil)).
  Intros.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in H12, H13.
  rewrite app_Znth1 in H by lia.
  rewrite app_Znth1 in H by lia.
  rewrite <- derivable1_orp_intros2.
  unfold match_progress, match_prefix, mismatch_prefix in *.
  split_pure_spatial.
  - cancel (CharArray.full str_pre (n + 1) (l ++ 0 :: nil)).
    cancel (CharArray.full substring_pre (m + 1) (sub ++ 0 :: nil)).
  - entailer!.
    destruct H11 as [Hprefix _].
    assert (Hpref: forall k : Z, 0 <= k < j -> Znth (i + k) l 0 = Znth k sub 0).
    { intros k Hk. apply Hprefix; lia. }
    intros _. intros k Hk.
    destruct (Z_lt_ge_dec k j) as [Hlt | Hge].
    + apply Hpref. lia.
    + assert (k = j) by lia. subst k. exact H.
Qed.

Lemma proof_of_p018_how_many_times_entail_wit_3_4 : p018_how_many_times_entail_wit_3_4.
Proof.
  pre_process.
  prop_apply (CharArray.full_Zlength substring_pre (m + 1) (sub ++ 0 :: nil)).
  Intros.
  prop_apply (CharArray.full_Zlength str_pre (n + 1) (l ++ 0 :: nil)).
  Intros.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in H12, H13.
  rewrite app_Znth1 in H by lia.
  rewrite app_Znth1 in H by lia.
  rewrite <- derivable1_orp_intros1.
  unfold match_progress, match_prefix, mismatch_prefix in *.
  split_pure_spatial.
  - cancel (CharArray.full str_pre (n + 1) (l ++ 0 :: nil)).
    cancel (CharArray.full substring_pre (m + 1) (sub ++ 0 :: nil)).
  - entailer!.
    destruct H11 as [_ Hmismatch].
    intros _.
    specialize (Hmismatch H10).
    destruct Hmismatch as [k [Hk1 Hk2]].
    exists k. split; [lia | exact Hk2].
Qed.

Lemma proof_of_p018_how_many_times_entail_wit_4_1 : p018_how_many_times_entail_wit_4_1.
Proof.
  pre_process.
  prop_apply (CharArray.full_Zlength substring_pre (m + 1) (sub ++ 0 :: nil)).
  Intros.
  prop_apply (CharArray.full_Zlength str_pre (n + 1) (l ++ 0 :: nil)).
  Intros.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in *.
  assert (Hzs : Zlength sub = m) by lia.
  assert (Hzl : Zlength l = n) by lia.
  rewrite <- derivable1_orp_intros1.
  unfold match_progress, match_prefix, mismatch_prefix, match_at_zb in *.
  split_pure_spatial.
  - cancel (CharArray.full str_pre (n + 1) (l ++ 0 :: nil)).
    cancel (CharArray.full substring_pre (m + 1) (sub ++ 0 :: nil)).
  - entailer!.
    assert (Hj : j = m) by lia.
    subst j.
    match goal with
    | Hmp : (_ /\ _) |- _ => destruct Hmp as [Hprefix _]
    end.
    assert (Hsubeq : sublist i (i + m) l = sub).
    {
      apply list_eq_ext with (d := 0).
      split.
      - rewrite Zlength_sublist.
        2: { split; lia. }
        rewrite Hzs.
        lia.
      - intros k Hk.
        assert (Hk' : 0 <= k < m).
        {
          rewrite Zlength_sublist in Hk.
          2: { split; lia. }
          lia.
        }
        rewrite (Znth_sublist 0 i k (i + m) l) by lia.
        replace (k + i) with (i + k) by lia.
        apply Hprefix; lia.
    }
    assert (Hrefl : list_eq_zb sub sub = true).
    {
      clear -sub.
      induction sub as [| a sub IH]; simpl; rewrite ?Z.eqb_refl, ?IH; reflexivity.
    }
    subst out.
    unfold count_matches_upto.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    simpl.
    assert (Hi_nat : Z.of_nat (Z.to_nat i) = i) by lia.
    rewrite Hi_nat.
    unfold match_at_zb.
    rewrite Hzs, Hzl.
    replace (Z.ltb 0 m) with true.
    2: { symmetry. apply Z.ltb_lt. lia. }
    replace (Z.leb (i + m) n) with true.
    2: { symmetry. apply Z.leb_le. lia. }
    rewrite Hsubeq, Hrefl.
    simpl.
    lia.
Qed.

Lemma proof_of_p018_how_many_times_entail_wit_4_2 : p018_how_many_times_entail_wit_4_2.
Proof.
  pre_process.
  prop_apply (CharArray.full_Zlength substring_pre (m + 1) (sub ++ 0 :: nil)).
  Intros.
  prop_apply (CharArray.full_Zlength str_pre (n + 1) (l ++ 0 :: nil)).
  Intros.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in *.
  assert (Hzs : Zlength sub = m) by lia.
  assert (Hzl : Zlength l = n) by lia.
  rewrite <- derivable1_orp_intros2.
  unfold match_progress, match_prefix, mismatch_prefix, match_at_zb in *.
  split_pure_spatial.
  - cancel (CharArray.full str_pre (n + 1) (l ++ 0 :: nil)).
    cancel (CharArray.full substring_pre (m + 1) (sub ++ 0 :: nil)).
  - entailer!.
    assert (Hj : j = m) by lia.
    subst j.
    match goal with
    | Hmp : (_ /\ _) |- _ => destruct Hmp as [_ Hmismatch]
    end.
    assert (Hex : exists k, 0 <= k < m /\ Znth (i + k) l 0 <> Znth k sub 0).
    {
      apply Hmismatch.
      lia.
    }
    assert (Hlist_true : forall l1 l2, list_eq_zb l1 l2 = true -> l1 = l2).
    {
      induction l1 as [| a l1 IH]; destruct l2 as [| b l2]; simpl; intros Heq; auto; try discriminate.
      apply andb_true_iff in Heq as [Hab Htl].
      apply Z.eqb_eq in Hab.
      specialize (IH _ Htl).
      subst. reflexivity.
    }
    assert (Hmatch_false : match_at_zb i l sub = false).
    {
      unfold match_at_zb.
      rewrite Hzs, Hzl.
      replace (Z.ltb 0 m) with true.
      2: { symmetry. apply Z.ltb_lt. lia. }
      replace (Z.leb (i + m) n) with true.
      2: { symmetry. apply Z.leb_le. lia. }
      destruct (list_eq_zb (sublist i (i + m) l) sub) eqn:Heq; auto.
      exfalso.
      apply Hlist_true in Heq.
      destruct Hex as [k [Hk1 Hk2]].
      rewrite <- Heq in Hk2.
      rewrite Znth_sublist in Hk2 by lia.
      replace (k + i) with (i + k) in Hk2 by lia.
      apply Hk2.
      reflexivity.
    }
    subst out.
    unfold count_matches_upto.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    simpl.
    assert (Hi_nat : Z.of_nat (Z.to_nat i) = i) by lia.
    rewrite Hi_nat.
    rewrite Hmatch_false.
    lia.
Qed.

Lemma count_matches_upto_nat_suffix_false :
  forall (start extra : nat) l sub,
    (forall t : nat, (t < extra)%nat -> match_at_zb (Z.of_nat (start + t)) l sub = false) ->
    count_matches_upto_nat (start + extra) l sub = count_matches_upto_nat start l sub.
Proof.
  intros start extra l sub Hfalse.
  induction extra as [| extra IHextra].
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - replace (start + S extra)%nat with (S (start + extra)) by lia.
    simpl.
    rewrite IHextra.
    + rewrite Hfalse by lia. lia.
    + intros t Ht. apply Hfalse. lia.
Qed.

Lemma match_at_zb_too_late_false :
  forall i n m l sub,
    Zlength l = n ->
    Zlength sub = m ->
    1 <= m ->
    n - m < i ->
    match_at_zb i l sub = false.
Proof.
  intros i n m l sub Hl Hs Hm Hi.
  unfold match_at_zb.
  rewrite Hs, Hl.
  replace (Z.ltb 0 m) with true.
  2: { symmetry. apply Z.ltb_lt. lia. }
  replace (Z.leb (i + m) n) with false.
  2: { symmetry. apply Z.leb_gt. lia. }
  reflexivity.
Qed.

Lemma proof_of_p018_how_many_times_return_wit_1 : p018_how_many_times_return_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - entailer!.
    prop_apply (CharArray.full_Zlength str_pre (n + 1) (l ++ 0 :: nil)).
    Intros.
    prop_apply (CharArray.full_Zlength substring_pre (m + 1) (sub ++ 0 :: nil)).
    Intros.
    rewrite Zlength_app, Zlength_cons, Zlength_nil in *.
    assert (Hi : i = n - m + 1) by lia.
    unfold problem_18_spec.
    match goal with
    | Hout : out = count_matches_upto i l sub |- _ => rewrite Hout
    end.
    unfold count_matches_upto.
    rewrite Hi.
    assert (Hsplit_nat :
      Z.to_nat n = Z.to_nat (n - m + 1) + (Z.to_nat n - Z.to_nat (n - m + 1))) by lia.
    rewrite Hsplit_nat.
    rewrite count_matches_upto_nat_suffix_false.
    + reflexivity.
    + intros t Ht.
      apply match_at_zb_too_late_false with (n := n) (m := m); try lia.
      * lia.
      * lia.
Qed.

Lemma proof_of_p018_how_many_times_return_wit_2 : p018_how_many_times_return_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - entailer!.
    prop_apply (CharArray.full_Zlength str_pre (n + 1) (l ++ 0 :: nil)).
    Intros.
    prop_apply (CharArray.full_Zlength substring_pre (m + 1) (sub ++ 0 :: nil)).
    Intros.
    rewrite Zlength_app, Zlength_cons, Zlength_nil in *.
    assert (Hi : i = n - m + 1) by lia.
    unfold problem_18_spec.
    match goal with
    | Hout : out = count_matches_upto i l sub |- _ => rewrite Hout
    end.
    unfold count_matches_upto.
    rewrite Hi.
    assert (Hsplit_nat :
      Z.to_nat n = Z.to_nat (n - m + 1) + (Z.to_nat n - Z.to_nat (n - m + 1))) by lia.
    rewrite Hsplit_nat.
    rewrite count_matches_upto_nat_suffix_false.
    + reflexivity.
    + intros t Ht.
      apply match_at_zb_too_late_false with (n := n) (m := m); try lia.
      * lia.
      * lia.
Qed.

Lemma proof_of_p018_how_many_times_return_wit_3 : p018_how_many_times_return_wit_3.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - entailer!.
    unfold problem_18_spec, count_matches_upto.
    assert (Hzero : forall fuel, fuel <= Z.to_nat n -> count_matches_upto_nat fuel l sub = 0).
    {
      induction fuel as [| fuel IH]; intros Hfuel; simpl; auto.
      rewrite IH by lia.
      rewrite H9, H8.
      rewrite Z.ltb_lt by lia.
      assert (Z.leb (Z.of_nat fuel + m) n = false).
      { apply Z.leb_gt. lia. }
      rewrite H.
      reflexivity.
    }
    rewrite Hzero by lia.
    reflexivity.
Qed.

Lemma proof_of_p018_how_many_times_return_wit_4 : p018_how_many_times_return_wit_4.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - entailer!.
    assert (Hm0 : m = 0) by lia.
    unfold problem_18_spec, count_matches_upto.
    assert (Hzero : forall fuel, count_matches_upto_nat fuel l sub = 0).
    {
      induction fuel as [| fuel IH]; simpl; auto.
      rewrite IH.
      rewrite H8, Hm0.
      simpl.
      reflexivity.
    }
    rewrite Hzero.
    reflexivity.
Qed.

Lemma proof_of_p018_how_many_times_return_wit_5 : p018_how_many_times_return_wit_5.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - entailer!.
    unfold problem_18_spec, count_matches_upto.
    rewrite Z2Nat.id by lia.
    simpl.
    reflexivity.
Qed.

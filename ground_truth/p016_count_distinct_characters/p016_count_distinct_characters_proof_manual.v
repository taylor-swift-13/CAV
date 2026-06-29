Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p016_count_distinct_characters Require Import p016_count_distinct_characters_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.

Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Import naive_C_Rules.
Require Import p016_count_distinct_characters.
Local Open Scope sac.

Lemma proof_of_p016_count_distinct_characters_entail_wit_1 : p016_count_distinct_characters_entail_wit_1.
Proof.
  pre_process.
  subst retval.
  entailer!.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_2_1 : p016_count_distinct_characters_entail_wit_2_1.
Proof.
  pre_process.
  entailer!.
  - unfold lower_seen_state.
    repeat split.
    + left; reflexivity.
    + assert (Hi : i < Zlength l) by lia.
      rewrite app_Znth1 in H by lia.
      rewrite app_Znth1 in H0 by lia.
      rewrite app_Znth1 by lia.
      unfold lower, is_upper_zb.
      assert (Hb1 : Z.leb 65 (Znth i l 0) = true).
      { apply Z.leb_le; lia. }
      assert (Hb2 : Z.leb (Znth i l 0) 90 = true).
      { apply Z.leb_le; lia. }
      rewrite Hb1, Hb2.
      reflexivity.
    + intros Hfalse. lia.
    + intros _ k Hk. lia.
  - assert (Hi : i < Zlength l) by lia.
    rewrite app_Znth1 in H by lia.
    rewrite app_Znth1 in H0 by lia.
    rewrite app_Znth1 by lia.
    unfold lower, is_upper_zb.
    assert (Hb1 : Z.leb 65 (Znth i l 0) = true).
    { apply Z.leb_le; lia. }
    assert (Hb2 : Z.leb (Znth i l 0) 90 = true).
    { apply Z.leb_le; lia. }
    rewrite Hb1, Hb2.
    reflexivity.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_2_2 : p016_count_distinct_characters_entail_wit_2_2.
Proof.
  pre_process.
  entailer!.
  - unfold lower_seen_state.
    repeat split.
    + left; reflexivity.
    + assert (Hi : i < Zlength l) by lia.
      rewrite app_Znth1 in H by lia.
      rewrite app_Znth1 by lia.
      unfold lower, is_upper_zb.
      assert (Hb : Z.leb 65 (Znth i l 0) = false).
      { apply Z.leb_gt; lia. }
      rewrite Hb.
      reflexivity.
    + intros Hfalse. lia.
    + intros _ k Hk. lia.
  - assert (Hi : i < Zlength l) by lia.
    rewrite app_Znth1 in H by lia.
    rewrite app_Znth1 by lia.
    unfold lower, is_upper_zb.
    assert (Hb : Z.leb 65 (Znth i l 0) = false).
    { apply Z.leb_gt; lia. }
    rewrite Hb.
    reflexivity.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_2_3 : p016_count_distinct_characters_entail_wit_2_3.
Proof.
  pre_process.
  entailer!.
  - unfold lower_seen_state.
    repeat split.
    + left; reflexivity.
    + assert (Hi : i < Zlength l) by lia.
      rewrite app_Znth1 in H by lia.
      rewrite app_Znth1 in H0 by lia.
      rewrite app_Znth1 by lia.
      unfold lower, is_upper_zb.
      assert (Hb1 : Z.leb 65 (Znth i l 0) = true).
      { apply Z.leb_le; lia. }
      assert (Hb2 : Z.leb (Znth i l 0) 90 = false).
      { apply Z.leb_gt; lia. }
      rewrite Hb1, Hb2.
      reflexivity.
    + intros Hfalse. lia.
    + intros _ k Hk. lia.
  - assert (Hi : i < Zlength l) by lia.
    rewrite app_Znth1 in H by lia.
    rewrite app_Znth1 in H0 by lia.
    rewrite app_Znth1 by lia.
    unfold lower, is_upper_zb.
    assert (Hb1 : Z.leb 65 (Znth i l 0) = true).
    { apply Z.leb_le; lia. }
    assert (Hb2 : Z.leb (Znth i l 0) 90 = false).
    { apply Z.leb_gt; lia. }
    rewrite Hb1, Hb2.
    reflexivity.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_3_1 : p016_count_distinct_characters_entail_wit_3_1.
Proof.
  pre_process.
  entailer!.
  unfold lower_seen_state.
  repeat split.
  - right; reflexivity.
  - exact H13.
  - intros _.
    exists j.
    split; [lia |].
    assert (Hj : j < Zlength l) by lia.
    rewrite app_Znth1 in H by lia.
    rewrite app_Znth1 in H0 by lia.
    rewrite app_Znth1 in H1 by lia.
    unfold lower, is_upper_zb.
    assert (Hb1 : Z.leb 65 (Znth j l 0) = true).
    { apply Z.leb_le; lia. }
    assert (Hb2 : Z.leb (Znth j l 0) 90 = true).
    { apply Z.leb_le; lia. }
    rewrite Hb1, Hb2.
    exact H.
  - intros Hfalse. lia.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_3_2 : p016_count_distinct_characters_entail_wit_3_2.
Proof.
  pre_process.
  entailer!.
  unfold lower_seen_state.
  repeat split.
  - right; reflexivity.
  - exact H12.
  - intros _.
    exists j.
    split; [lia |].
    assert (Hj : j < Zlength l) by lia.
    rewrite app_Znth1 in H by lia.
    rewrite app_Znth1 in H0 by lia.
    unfold lower, is_upper_zb.
    assert (Hb : Z.leb 65 (Znth j l 0) = false).
    { apply Z.leb_gt; lia. }
    rewrite Hb.
    exact H.
  - intros Hfalse. lia.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_3_3 : p016_count_distinct_characters_entail_wit_3_3.
Proof.
  pre_process.
  entailer!.
  unfold lower_seen_state.
  repeat split.
  - right; reflexivity.
  - exact H13.
  - intros _.
    exists j.
    split; [lia |].
    assert (Hj : j < Zlength l) by lia.
    rewrite app_Znth1 in H by lia.
    rewrite app_Znth1 in H0 by lia.
    rewrite app_Znth1 in H1 by lia.
    unfold lower, is_upper_zb.
    assert (Hb1 : Z.leb 65 (Znth j l 0) = true).
    { apply Z.leb_le; lia. }
    assert (Hb2 : Z.leb (Znth j l 0) 90 = false).
    { apply Z.leb_gt; lia. }
    rewrite Hb1, Hb2.
    exact H.
  - intros Hfalse. lia.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_3_4 : p016_count_distinct_characters_entail_wit_3_4.
Proof.
  pre_process.
  entailer!.
  unfold lower_seen_state in *.
  destruct H16 as [[Hseen0 | Hseen1] [Hc [Hyes Hno]]].
  - repeat split.
    + left; exact Hseen0.
    + exact H13.
    + intros Hs. lia.
    + intros _ k Hk.
      assert (Hcase : k < j \/ k = j) by lia.
      destruct Hcase as [Hlt | Heq].
      * apply (Hno Hseen0); lia.
      * subst k.
        assert (Hj : j < Zlength l) by lia.
        rewrite app_Znth1 in H by lia.
        rewrite app_Znth1 in H0 by lia.
        rewrite app_Znth1 in H1 by lia.
        unfold lower, is_upper_zb.
        assert (Hb1 : Z.leb 65 (Znth j l 0) = true).
        { apply Z.leb_le; lia. }
        assert (Hb2 : Z.leb (Znth j l 0) 90 = false).
        { apply Z.leb_gt; lia. }
        rewrite Hb1, Hb2.
        exact H.
  - repeat split.
    + right; exact Hseen1.
    + exact H13.
    + intros _.
      destruct (Hyes Hseen1) as [k [Hk Hkc]].
      exists k.
      split; lia.
    + intros Hs. lia.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_3_5 : p016_count_distinct_characters_entail_wit_3_5.
Proof.
  pre_process.
  entailer!.
  unfold lower_seen_state in *.
  destruct H15 as [[Hseen0 | Hseen1] [Hc [Hyes Hno]]].
  - repeat split.
    + left; exact Hseen0.
    + exact H12.
    + intros Hs. lia.
    + intros _ k Hk.
      assert (Hcase : k < j \/ k = j) by lia.
      destruct Hcase as [Hlt | Heq].
      * apply (Hno Hseen0); lia.
      * subst k.
        assert (Hj : j < Zlength l) by lia.
        rewrite app_Znth1 in H by lia.
        rewrite app_Znth1 in H0 by lia.
        unfold lower, is_upper_zb.
        assert (Hb : Z.leb 65 (Znth j l 0) = false).
        { apply Z.leb_gt; lia. }
        rewrite Hb.
        exact H.
  - repeat split.
    + right; exact Hseen1.
    + exact H12.
    + intros _.
      destruct (Hyes Hseen1) as [k [Hk Hkc]].
      exists k.
      split; lia.
    + intros Hs. lia.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_3_6 : p016_count_distinct_characters_entail_wit_3_6.
Proof.
  pre_process.
  entailer!.
  unfold lower_seen_state in *.
  destruct H16 as [[Hseen0 | Hseen1] [Hc [Hyes Hno]]].
  - repeat split.
    + left; exact Hseen0.
    + exact H13.
    + intros Hs. lia.
    + intros _ k Hk.
      assert (Hcase : k < j \/ k = j) by lia.
      destruct Hcase as [Hlt | Heq].
      * apply (Hno Hseen0); lia.
      * subst k.
        assert (Hj : j < Zlength l) by lia.
        rewrite app_Znth1 in H by lia.
        rewrite app_Znth1 in H0 by lia.
        rewrite app_Znth1 in H1 by lia.
        unfold lower, is_upper_zb.
        assert (Hb1 : Z.leb 65 (Znth j l 0) = true).
        { apply Z.leb_le; lia. }
        assert (Hb2 : Z.leb (Znth j l 0) 90 = true).
        { apply Z.leb_le; lia. }
        rewrite Hb1, Hb2.
        exact H.
  - repeat split.
    + right; exact Hseen1.
    + exact H13.
    + intros _.
      destruct (Hyes Hseen1) as [k [Hk Hkc]].
      exists k.
      split; lia.
    + intros Hs. lia.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_4_1 : p016_count_distinct_characters_entail_wit_4_1.
Proof.
  pre_process.
  match goal with
  | H : lower_seen_state j i l c seen |- _ => pose proof H as Hstate
  end.
  match goal with
  | H : count = count_distinct_lower_upto i l |- _ => pose proof H as Hcount
  end.
  match goal with
  | H : Zlength l = len |- _ => pose proof H as Hzlen
  end.
  assert (Hji : j = i) by lia.
  subst j.
  subst seen.
  unfold lower_seen_state in Hstate.
  destruct Hstate as [[_ | Hbad] [Hc [_ Hno]]].
  2: lia.
  specialize (Hno eq_refl).
  assert (Hcollect_app :
    forall seen0 xs ys,
      collect_lower seen0 (xs ++ ys) =
      collect_lower (collect_lower seen0 xs) ys).
  {
    intros seen0 xs.
    revert seen0.
    induction xs as [|a xs IH]; intros seen0 ys; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
  }
  assert (Hmem_false :
    forall pref seen0,
      mem_zb c seen0 = false ->
      (forall k, 0 <= k < Zcomplements.Zlength pref ->
         lower (Positional.Znth k pref 0) <> c) ->
      mem_zb c (collect_lower seen0 pref) = false).
  {
    intros pref.
    induction pref as [|a pref IH]; intros seen0 Hseen Hpref; simpl.
    - exact Hseen.
    - assert (Ha : lower a <> c).
      {
        specialize (Hpref 0).
        assert (Hrange0 : 0 <= 0 < Zcomplements.Zlength (a :: pref)).
        {
          pose proof (Length.Zlength_nonneg pref) as Hlen_nonneg.
          rewrite Zcomplements.Zlength_cons.
          lia.
        }
        specialize (Hpref Hrange0).
        exact Hpref.
      }
      assert (Htail :
        forall k, 0 <= k < Zcomplements.Zlength pref ->
          lower (Positional.Znth k pref 0) <> c).
      {
        intros k Hk.
        specialize (Hpref (k + 1)).
        assert (Hrange_succ : 0 <= k + 1 < Zcomplements.Zlength (a :: pref)).
        {
          rewrite Zcomplements.Zlength_cons.
          lia.
        }
        specialize (Hpref Hrange_succ).
        rewrite Positional.Znth_cons in Hpref by lia.
        replace (k + 1 - 1) with k in Hpref by lia.
        exact Hpref.
      }
      unfold add_unique.
      destruct (mem_zb (lower a) seen0) eqn:Hseen_a.
      + apply IH; assumption.
      + assert (Hseed_false : mem_zb c (lower a :: seen0) = false).
        {
          simpl.
          assert (Hneq : Z.eqb c (lower a) = false).
          {
            apply Z.eqb_neq.
            congruence.
          }
          rewrite Hneq.
          exact Hseen.
        }
        apply IH.
        * exact Hseed_false.
        * exact Htail.
  }
  assert (Hpref_len :
    Zcomplements.Zlength (sublist 0 i l) = i).
  {
    apply Length.Zlength_sublist0.
    rewrite Hzlen.
    lia.
  }
  assert (Hno_pref :
    forall k, 0 <= k < Zcomplements.Zlength (sublist 0 i l) ->
      lower (Znth k (sublist 0 i l) 0) <> c).
  {
    intros k Hk.
    rewrite (Length.Znth_sublist_lt 0 0 i l k).
    3: {
      rewrite Hpref_len in Hk.
      lia.
    }
    2: {
      lia.
    }
    2: lia.
    apply Hno.
    rewrite Hpref_len in Hk.
    lia.
  }
  entailer!.
  rewrite Hcount.
  unfold count_distinct_lower_upto, distinct_lower_prefix.
  assert (Hsplit :
    sublist 0 (i + 1) l =
    (sublist 0 i l ++ Znth i l 0 :: nil)%list).
  {
    rewrite (Length.sublist_split 0 (i + 1) i l).
    2: lia.
    2: lia.
    rewrite (Length.sublist_single 0 i l).
    2: lia.
    reflexivity.
  }
  rewrite Hsplit.
  rewrite Hcollect_app.
  simpl.
  assert (Hclower : lower (Znth i l 0) = c) by (symmetry; exact Hc).
  rewrite Hclower.
  unfold add_unique.
  assert (Hmem :
    mem_zb c (collect_lower nil (sublist 0 i l)) = false).
  {
    apply Hmem_false.
    - reflexivity.
    - exact Hno_pref.
  }
  rewrite Hmem.
  simpl.
  lia.
Qed.

Lemma proof_of_p016_count_distinct_characters_entail_wit_4_2 : p016_count_distinct_characters_entail_wit_4_2.
Proof.
  pre_process.
  match goal with
  | H : lower_seen_state j i l c seen |- _ => pose proof H as Hstate
  end.
  match goal with
  | H : count = count_distinct_lower_upto i l |- _ => pose proof H as Hcount
  end.
  match goal with
  | H : Zlength l = len |- _ => pose proof H as Hzlen
  end.
  match goal with
  | H : seen <> 0 |- _ => pose proof H as Hseen_nz
  end.
  assert (Hji : j = i) by lia.
  subst j.
  unfold lower_seen_state in Hstate.
  destruct Hstate as [[Hzero | Hone] [Hc [Hex _]]].
  - contradiction.
  - subst seen.
    specialize (Hex eq_refl).
    assert (Hcollect_app :
      forall seen0 xs ys,
        collect_lower seen0 (xs ++ ys) =
        collect_lower (collect_lower seen0 xs) ys).
    {
      intros seen0 xs.
      revert seen0.
      induction xs as [|a xs IH]; intros seen0 ys; simpl.
      - reflexivity.
      - rewrite IH. reflexivity.
    }
    assert (Hmem_keep :
      forall pref seen0,
        mem_zb c seen0 = true ->
        mem_zb c (collect_lower seen0 pref) = true).
    {
      intros pref.
      induction pref as [|a pref IH]; intros seen0 Hseen; simpl.
      - exact Hseen.
      - unfold add_unique.
        destruct (mem_zb (lower a) seen0) eqn:Hseen_a.
        + apply IH. exact Hseen.
        + apply IH.
          simpl.
          destruct (Z.eqb c (lower a)).
          * reflexivity.
          * exact Hseen.
    }
    assert (Hmem_occ :
      forall pref seen0,
        (exists k, 0 <= k < Zcomplements.Zlength pref /\
           lower (Positional.Znth k pref 0) = c) ->
        mem_zb c (collect_lower seen0 pref) = true).
    {
      intros pref.
      induction pref as [|a pref IH]; intros seen0 [k [Hk Hkc]]; simpl in *.
      - rewrite Zcomplements.Zlength_nil in Hk.
        lia.
      - assert (Hcase : k = 0 \/ 0 < k) by lia.
        destruct Hcase as [Hk0 | Hkpos].
        + subst k.
          rewrite Positional.Znth0_cons in Hkc.
          unfold add_unique.
          destruct (mem_zb (lower a) seen0) eqn:Hseen_a.
          * apply Hmem_keep.
            rewrite <- Hkc.
            exact Hseen_a.
          * apply Hmem_keep.
            simpl.
            rewrite Hkc, Z.eqb_refl.
            reflexivity.
        + unfold add_unique.
          destruct (mem_zb (lower a) seen0) eqn:Hseen_a.
          * apply IH.
            exists (k - 1).
            split.
            {
              rewrite Zcomplements.Zlength_cons in Hk.
              lia.
            }
            rewrite Positional.Znth_cons in Hkc by lia.
            replace (k - 1) with (k - 1) in Hkc by lia.
            exact Hkc.
          * apply IH with (seen0 := lower a :: seen0).
            exists (k - 1).
            split.
            {
              rewrite Zcomplements.Zlength_cons in Hk.
              lia.
            }
            rewrite Positional.Znth_cons in Hkc by lia.
            replace (k - 1) with (k - 1) in Hkc by lia.
            exact Hkc.
    }
    assert (Hpref_len :
      Zcomplements.Zlength (sublist 0 i l) = i).
    {
      apply Length.Zlength_sublist0.
      rewrite Hzlen.
      lia.
    }
    entailer!.
    rewrite Hcount.
    unfold count_distinct_lower_upto, distinct_lower_prefix.
    assert (Hsplit :
      sublist 0 (i + 1) l =
      (sublist 0 i l ++ Znth i l 0 :: nil)%list).
    {
      rewrite (Length.sublist_split 0 (i + 1) i l).
      2: lia.
      2: lia.
      rewrite (Length.sublist_single 0 i l).
      2: lia.
      reflexivity.
    }
    rewrite Hsplit.
    rewrite Hcollect_app.
    simpl.
    assert (Hclower : lower (Znth i l 0) = c) by (symmetry; exact Hc).
    rewrite Hclower.
    unfold add_unique.
    assert (Hmem :
      mem_zb c (collect_lower nil (sublist 0 i l)) = true).
    {
      apply Hmem_occ.
      destruct Hex as [k [Hk Hkc]].
      exists k.
      split.
      - rewrite Hpref_len.
        exact Hk.
      - rewrite (Length.Znth_sublist_lt 0 0 i l k).
        3: lia.
        2: lia.
        2: lia.
        exact Hkc.
    }
    rewrite Hmem.
    lia.
Qed.

Lemma proof_of_p016_count_distinct_characters_return_wit_1 : p016_count_distinct_characters_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = len) by lia.
  subst i.
  entailer!.
  unfold problem_16_spec.
  rewrite H9.
  unfold count_distinct_lower_upto, distinct_lower_prefix.
  rewrite (sublist_self l len) by (symmetry; exact H2).
  rewrite <- Zcomplements.Zlength_correct.
  reflexivity.
Qed.

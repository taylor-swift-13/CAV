Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
From AUXLib Require Import ListLib.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Coq.micromega.Lia.
Require Import p114_minSubArraySum.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Lemma fold_left_add_const :
  forall (l : list Z) (a : Z),
    fold_left Z.add l a = a + fold_left Z.add l 0.
Proof.
  induction l as [|b l IH]; intros a; simpl.
  - lia.
  - rewrite IH. rewrite (IH b). lia.
Qed.

Lemma list_sum_eq_sum :
  forall (l : list Z), list_sum l = sum l.
Proof.
  induction l as [|a l IH]; simpl.
  - reflexivity.
  - unfold list_sum in *. simpl in *.
    rewrite fold_left_add_const.
    rewrite IH. lia.
Qed.

Lemma sum_app_list_sum :
  forall l1 l2, list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
Proof.
  intros. repeat rewrite list_sum_eq_sum. apply sum_app.
Qed.

Lemma min_suffix_prefix_step :
  forall (i : Z) (nums : list Z),
    1 <= i < Zlength nums ->
    min_suffix_prefix (i + 1) nums =
    if Z.ltb (min_suffix_prefix i nums) 0
    then min_suffix_prefix i nums + Znth i nums 0
    else Znth i nums 0.
Proof.
  intros i nums Hi.
  unfold min_suffix_prefix.
  assert (Hnat: Z.to_nat (i + 1) = S (Z.to_nat i)).
  { rewrite Z2Nat.inj_add by lia. replace (Z.to_nat 1) with 1%nat by reflexivity.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hnat.
  destruct (Z.to_nat i) as [|n] eqn:Hn.
  - exfalso. lia.
  - simpl.
    assert (Hpos: Z.pos (Pos.of_succ_nat n) = i).
    { assert (H0: Z.of_nat (Z.to_nat i) = i) by (apply Z2Nat.id; lia).
      rewrite <- H0. rewrite Hn. reflexivity. }
    rewrite Hpos.
    replace (i - 1 + 1) with i by lia.
    reflexivity.
Qed.

Lemma min_subarray_prefix_step :
  forall (i : Z) (nums : list Z),
    1 <= i < Zlength nums ->
    min_subarray_prefix (i + 1) nums =
    if Z.ltb (min_suffix_prefix (i + 1) nums) (min_subarray_prefix i nums)
    then min_suffix_prefix (i + 1) nums
    else min_subarray_prefix i nums.
Proof.
  intros i nums Hi.
  unfold min_subarray_prefix, min_suffix_prefix.
  assert (Hnat: Z.to_nat (i + 1) = S (Z.to_nat i)).
  { rewrite Z2Nat.inj_add by lia. replace (Z.to_nat 1) with 1%nat by reflexivity.
    rewrite Nat.add_1_r. reflexivity. }
  rewrite Hnat.
  destruct (Z.to_nat i) as [|n] eqn:Hn.
  - exfalso. lia.
  - simpl.
    assert (Hpos: Z.pos (Pos.of_succ_nat n) = i).
    { assert (H0: Z.of_nat (Z.to_nat i) = i) by (apply Z2Nat.id; lia).
      rewrite <- H0. rewrite Hn. reflexivity. }
    rewrite Hpos.
    replace (i - 1 + 1) with i by lia.
    reflexivity.
Qed.

Lemma min_suffix_prefix_1 :
  forall (nums : list Z),
    1 <= Zlength nums ->
    min_suffix_prefix 1 nums = Znth 0 nums 0.
Proof.
  intros nums H.
  unfold min_suffix_prefix.
  simpl. reflexivity.
Qed.

Lemma min_subarray_prefix_1 :
  forall (nums : list Z),
    1 <= Zlength nums ->
    min_subarray_prefix 1 nums = Znth 0 nums 0.
Proof.
  intros nums H.
  unfold min_subarray_prefix.
  simpl. reflexivity.
Qed.

Lemma sublist_full_self :
  forall (l : list Z), sublist 0 (Zlength l) l = l.
Proof.
  intros l.
  unfold sublist.
  rewrite Zlength_correct.
  replace (Z.to_nat (Z.of_nat (length l))) with (length l) by (symmetry; apply Nat2Z.id).
  rewrite skipn_O.
  apply firstn_all.
Qed.

Lemma sublist_eq_app :
  forall (lo hi : Z) (nums : list Z),
    0 <= lo <= hi -> hi <= Zlength nums ->
    nums = sublist 0 lo nums ++ sublist lo hi nums ++ sublist hi (Zlength nums) nums.
Proof.
  intros lo hi nums Hlo Hhi.
  assert (H1: sublist 0 hi nums = sublist 0 lo nums ++ sublist lo hi nums).
  { rewrite <- (sublist_split 0 hi lo nums) by lia. reflexivity. }
  assert (H2: nums = sublist 0 hi nums ++ sublist hi (Zlength nums) nums).
  { rewrite <- (sublist_split 0 (Zlength nums) hi nums) by lia.
    rewrite sublist_full_self. reflexivity. }
  rewrite H1 in H2. rewrite <- app_assoc in H2. exact H2.
Qed.

Lemma problem_114_spec_sublist :
  forall (nums : list Z) (result : Z),
    problem_114_spec nums result <->
    ((exists lo hi, 0 <= lo < hi /\ hi <= Zlength nums /\ sum (sublist lo hi nums) = result)
     /\
     (forall lo hi, 0 <= lo < hi -> hi <= Zlength nums -> result <= sum (sublist lo hi nums))).
Proof.
  intros nums result. unfold problem_114_spec. split; intros [Hex Hmin]; split.
  - destruct Hex as [sub_array [Hneq [[prefix [suffix Happ]] Hsum]]].
    exists (Zlength prefix), (Zlength prefix + Zlength sub_array).
    split; [|split].
    + assert (0 <= Zlength prefix) by apply Zlength_nonneg.
      assert (Zlength sub_array > 0).
      { destruct sub_array; [contradiction |]. rewrite Zlength_cons. pose proof (Zlength_nonneg sub_array). lia. }
      lia.
    + assert (Zlength prefix + Zlength sub_array <= Zlength nums).
      { rewrite Happ. repeat rewrite Zlength_app. pose proof (Zlength_nonneg suffix). lia. }
      lia.
    + rewrite <- Hsum. rewrite Happ.
      assert (sublist (Zlength prefix) (Zlength prefix + Zlength sub_array) (prefix ++ sub_array ++ suffix) = sub_array) as Hsubeq.
      { pose proof (Zlength_nonneg prefix).
        pose proof (Zlength_nonneg sub_array).
        rewrite (sublist_split_app_r (Zlength prefix) (Zlength prefix + Zlength sub_array) (Zlength prefix) prefix (sub_array ++ suffix));
          [ | reflexivity | lia ].
        replace (Zlength prefix + Zlength sub_array - Zlength prefix) with (Zlength sub_array) by lia.
        replace (Zlength prefix - Zlength prefix) with 0 by lia.
        rewrite sublist_app_exact1. reflexivity. }
      rewrite Hsubeq. rewrite list_sum_eq_sum. reflexivity.
  - intros lo hi Hlo Hhi.
    specialize (Hmin (sublist lo hi nums)).
    assert (Hneq: sublist lo hi nums <> []).
    { intro Hc. assert (HZ: Zlength (sublist lo hi nums) = 0) by (rewrite Hc; apply Zlength_nil).
      rewrite Zlength_sublist in HZ by lia. lia. }
    assert (Hex': exists prefix suffix, nums = prefix ++ sublist lo hi nums ++ suffix).
    { exists (sublist 0 lo nums), (sublist hi (Zlength nums) nums).
      apply sublist_eq_app; lia. }
    specialize (Hmin Hneq Hex').
    rewrite list_sum_eq_sum in Hmin. exact Hmin.
  - destruct Hex as [lo [hi [Hlo [Hhi Hsum]]]].
    exists (sublist lo hi nums). split; [|split].
    + assert (sublist lo hi nums <> []).
      { intro Hc. assert (HZ: Zlength (sublist lo hi nums) = 0) by (rewrite Hc; apply Zlength_nil).
        rewrite Zlength_sublist in HZ by lia. lia. }
      auto.
    + exists (sublist 0 lo nums), (sublist hi (Zlength nums) nums).
      apply sublist_eq_app; lia.
    + rewrite list_sum_eq_sum. rewrite Hsum. reflexivity.
  - intros sub_array Hneq [prefix [suffix Happ]].
    assert (Hlo: 0 <= Zlength prefix).
    { apply Zlength_nonneg. }
    assert (Hhi: Zlength prefix + Zlength sub_array <= Zlength nums).
    { rewrite Happ. repeat rewrite Zlength_app. pose proof (Zlength_nonneg suffix). lia. }
    assert (Hlt: Zlength prefix < Zlength prefix + Zlength sub_array).
    { assert (Zlength sub_array > 0).
      { destruct sub_array; [contradiction | rewrite Zlength_cons; pose proof (Zlength_nonneg sub_array); lia]. }
      lia. }
    assert (Hbounds: 0 <= Zlength prefix < Zlength prefix + Zlength sub_array) by (split; [exact Hlo | exact Hlt]).
    specialize (Hmin (Zlength prefix) (Zlength prefix + Zlength sub_array) Hbounds Hhi).
    assert (Hsub: sub_array = sublist (Zlength prefix) (Zlength prefix + Zlength sub_array) nums).
    { rewrite Happ.
      pose proof (Zlength_nonneg prefix).
      pose proof (Zlength_nonneg sub_array).
      rewrite (sublist_split_app_r (Zlength prefix) (Zlength prefix + Zlength sub_array) (Zlength prefix) prefix (sub_array ++ suffix));
        [ | reflexivity | lia ].
      replace (Zlength prefix + Zlength sub_array - Zlength prefix) with (Zlength sub_array) by lia.
      replace (Zlength prefix - Zlength prefix) with 0 by lia.
      rewrite sublist_app_exact1. reflexivity. }
    rewrite list_sum_eq_sum. rewrite <- Hsub in Hmin. exact Hmin.
Qed.

(* Correctness of min_suffix_prefix: minimum suffix sum *)
Lemma min_suffix_prefix_spec :
  forall (n : Z) (nums : list Z),
    1 <= n <= Zlength nums ->
    (exists lo, 0 <= lo < n /\ sum (sublist lo n nums) = min_suffix_prefix n nums)
    /\
    (forall lo, 0 <= lo < n -> min_suffix_prefix n nums <= sum (sublist lo n nums)).
Proof.
  intros n nums Hn.
  replace n with (Z.of_nat (Z.to_nat n)) in * by (apply Z2Nat.id; lia).
  remember (Z.to_nat n) as m eqn:Hm.
  pose proof Hn as H.
  clear Hn Hm n.
  induction m as [|m' IH]; [exfalso; simpl in H; lia |].
  destruct m' as [|m''].
  - simpl. assert (Hsub: sublist 0 1 nums = [Znth 0 nums 0]) by (apply sublist_single; lia).
    split.
    + exists 0. split; [lia |].
      rewrite Hsub. unfold sum. simpl. rewrite min_suffix_prefix_1 by lia. lia.
    + intros lo Hlo.
      assert (lo = 0) by lia. subst lo.
      rewrite Hsub. unfold sum. simpl. rewrite min_suffix_prefix_1 by lia. lia.
  - assert (Hrec: 1 <= Z.of_nat (S m'') <= Zlength nums) by (simpl in *; lia).
    destruct IH as [IH1 IH2]; [lia |].
    assert (Hn1: Z.of_nat (S (S m'')) = Z.of_nat (S m'') + 1) by (simpl; lia).
    assert (Hsub: sublist (Z.of_nat (S m'')) (Z.of_nat (S m'') + 1) nums = [Znth (Z.of_nat (S m'')) nums 0]).
    { apply sublist_single. simpl. lia. }
    assert (Hstep: min_suffix_prefix (Z.of_nat (S (S m''))) nums =
      if Z.ltb (min_suffix_prefix (Z.of_nat (S m'')) nums) 0
      then min_suffix_prefix (Z.of_nat (S m'')) nums + Znth (Z.of_nat (S m'')) nums 0
      else Znth (Z.of_nat (S m'')) nums 0).
    { apply min_suffix_prefix_step. simpl. lia. }
    rewrite Hn1 in *.
    assert (Hsplit: forall lo, 0 <= lo < Z.of_nat (S m'') + 1 ->
      sum (sublist lo (Z.of_nat (S m'') + 1) nums) = sum (sublist lo (Z.of_nat (S m'')) nums) + Znth (Z.of_nat (S m'')) nums 0).
    { intros lo Hlo.
      assert (sublist lo (Z.of_nat (S m'') + 1) nums = sublist lo (Z.of_nat (S m'')) nums ++ sublist (Z.of_nat (S m'')) (Z.of_nat (S m'') + 1) nums).
      { apply sublist_split; simpl; lia. }
      rewrite H. rewrite sum_app. rewrite Hsub. unfold sum. simpl. lia. }
    split.
    + destruct IH1 as [lo [Hlo Hsum]].
      destruct (Z.ltb (min_suffix_prefix (Z.of_nat (S m'')) nums) 0) eqn:Hlt.
      * exists lo. split; [simpl; lia |].
        rewrite Hstep. rewrite Z.ltb_lt in Hlt.
        rewrite Hsplit by lia. lia.
      * exists (Z.of_nat (S m'')). split; [simpl; lia |].
        rewrite Hstep. rewrite Z.ltb_ge in Hlt.
        rewrite sublist_single by lia. unfold sum. simpl. lia.
    + intros lo Hlo.
      rewrite Hstep.
      destruct (Z.ltb (min_suffix_prefix (Z.of_nat (S m'')) nums) 0) eqn:Hlt.
      * rewrite Z.ltb_lt in Hlt.
        destruct (Z.eq_dec lo (Z.of_nat (S m''))) as [Heq | Hneq].
        -- subst lo. rewrite Hsplit by lia. lia.
        -- assert (lo < Z.of_nat (S m'')) by lia.
           rewrite Hsplit by lia.
           specialize (IH2 lo H0). lia.
      * rewrite Z.ltb_ge in Hlt.
        destruct (Z.eq_dec lo (Z.of_nat (S m''))) as [Heq | Hneq].
        -- subst lo. rewrite Hsplit by lia. lia.
        -- assert (lo < Z.of_nat (S m'')) by lia.
           rewrite Hsplit by lia.
           specialize (IH2 lo H0). lia.
Qed.

(* Correctness of min_subarray_prefix: minimum subarray sum *)
Lemma min_subarray_prefix_spec :
  forall (n : Z) (nums : list Z),
    1 <= n <= Zlength nums ->
    (exists lo hi, 0 <= lo < hi /\ hi <= n /\ sum (sublist lo hi nums) = min_subarray_prefix n nums)
    /\
    (forall lo hi, 0 <= lo < hi -> hi <= n -> min_subarray_prefix n nums <= sum (sublist lo hi nums)).
Proof.
  intros n nums Hn.
  replace n with (Z.of_nat (Z.to_nat n)) in * by (apply Z2Nat.id; lia).
  remember (Z.to_nat n) as m eqn:Hm.
  assert (1 <= Z.of_nat m <= Zlength nums) by (rewrite <- Hm; lia).
  clear Hn Hm n.
  induction m as [|m' IH]; [exfalso; simpl in H; lia |].
  destruct m' as [|m''].
  - simpl. assert (Hsub: sublist 0 1 nums = [Znth 0 nums 0]) by (apply sublist_single; lia).
    split.
    + exists 0, 1. split; [lia | split; [lia |]].
      rewrite Hsub. unfold sum. simpl. lia.
    + intros lo hi Hlo Hhi.
      assert (lo = 0 /\ hi = 1) by (split; lia). destruct H as [Hl Hh].
      subst lo hi. rewrite Hsub. unfold sum. simpl. lia.
  - assert (Hrec: 1 <= Z.of_nat (S m'') <= Zlength nums) by (simpl in *; lia).
    destruct IH as [IH1 IH2]; [lia |].
    assert (Hn1: Z.of_nat (S (S m'')) = Z.of_nat (S m'') + 1) by (simpl; lia).
    assert (Hstep: min_subarray_prefix (Z.of_nat (S (S m''))) nums =
      if Z.ltb (min_suffix_prefix (Z.of_nat (S m'') + 1) nums) (min_subarray_prefix (Z.of_nat (S m'')) nums)
      then min_suffix_prefix (Z.of_nat (S m'') + 1) nums
      else min_subarray_prefix (Z.of_nat (S m'')) nums).
    { rewrite Hn1. apply min_subarray_prefix_step. simpl. lia. }
    assert (Hsuf: min_suffix_prefix (Z.of_nat (S m'') + 1) nums =
      if Z.ltb (min_suffix_prefix (Z.of_nat (S m'')) nums) 0
      then min_suffix_prefix (Z.of_nat (S m'')) nums + Znth (Z.of_nat (S m'')) nums 0
      else Znth (Z.of_nat (S m'')) nums 0).
    { apply min_suffix_prefix_step. simpl. lia. }
    rewrite Hn1 in *.
    split.
    + destruct (Z.ltb (min_suffix_prefix (Z.of_nat (S m'') + 1) nums) (min_subarray_prefix (Z.of_nat (S m'')) nums)) eqn:Hlt.
      * assert (Hex: exists lo, 0 <= lo < Z.of_nat (S m'') + 1 /\
          sum (sublist lo (Z.of_nat (S m'') + 1) nums) = min_suffix_prefix (Z.of_nat (S m'') + 1) nums).
        { apply min_suffix_prefix_spec; simpl; lia. }
        destruct Hex as [lo [Hlo Hsum]].
        exists lo, (Z.of_nat (S m'') + 1).
        split; [lia | split; [lia |]].
        rewrite Hstep. rewrite Z.ltb_lt in Hlt. lia.
      * destruct IH1 as [lo [hi [Hlo [Hhi Hsum]]]].
        exists lo, hi.
        split; [lia | split; [lia |]].
        rewrite Hstep. rewrite Z.ltb_ge in Hlt. lia.
    + intros lo hi Hlo Hhi.
      rewrite Hstep.
      destruct (Z.ltb (min_suffix_prefix (Z.of_nat (S m'') + 1) nums) (min_subarray_prefix (Z.of_nat (S m'')) nums)) eqn:Hlt.
      * destruct (Z.eq_dec hi (Z.of_nat (S m'') + 1)) as [Heq | Hneq].
        -- subst hi. rewrite Z.ltb_lt in Hlt.
           assert (Hmin: min_suffix_prefix (Z.of_nat (S m'') + 1) nums <= sum (sublist lo (Z.of_nat (S m'') + 1) nums)).
           { apply min_suffix_prefix_spec; simpl; lia. }
           lia.
        -- assert (hi <= Z.of_nat (S m'')) by lia.
           specialize (IH2 lo hi Hlo H0).
           rewrite Z.ltb_lt in Hlt. lia.
      * destruct (Z.eq_dec hi (Z.of_nat (S m'') + 1)) as [Heq | Hneq].
        -- subst hi. rewrite Z.ltb_ge in Hlt.
           assert (Hmin: min_suffix_prefix (Z.of_nat (S m'') + 1) nums <= sum (sublist lo (Z.of_nat (S m'') + 1) nums)).
           { apply min_suffix_prefix_spec; simpl; lia. }
           lia.
        -- assert (hi <= Z.of_nat (S m'')) by lia.
           specialize (IH2 lo hi Hlo H0).
           rewrite Z.ltb_ge in Hlt. lia.
Qed.

(* Main correctness theorem *)
Lemma min_subarray_prefix_problem_spec :
  forall (nums : list Z),
    nums <> [] ->
    problem_114_spec nums (min_subarray_prefix (Zlength nums) nums).
Proof.
  intros nums Hneq.
  assert (Hn: 1 <= Zlength nums).
  { destruct nums; [contradiction | simpl; lia]. }
  assert (Hspec := min_subarray_prefix_spec (Zlength nums) nums ltac:(lia)).
  rewrite problem_114_spec_sublist.
  destruct Hspec as [Hex Hmin].
  split.
  - destruct Hex as [lo [hi [Hlo [Hhi Hsum]]]].
    exists lo, hi. split; [lia | split; [lia | exact Hsum]].
  - intros lo hi Hlo Hhi.
    apply Hmin; lia.
Qed.

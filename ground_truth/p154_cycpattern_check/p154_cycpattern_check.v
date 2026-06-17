(* spec/154 *)
(* def cycpattern_check(a , b):
"""You are given 2 words. You need to return True if the second word or any of its rotations is a substring in the first word
cycpattern_check("abcd","abd") => False
cycpattern_check("hello","ell") => True
cycpattern_check("whassup","psus") => False
cycpattern_check("abab","baa") => True
cycpattern_check("efef","eeff") => False
cycpattern_check("himenss","simen") => True

""" *)
(* 引入所需的基础库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Import ListNotations.

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

(* 定义：sub 是 main 的子串 *)
Definition is_substring (sub main : list ascii) : Prop :=
  exists prefix suffix, main = prefix ++ sub ++ suffix.

(* 定义：r 是 b 的一个循环旋转 *)
Definition is_rotation_of (r b : list ascii) : Prop :=
  exists p1 p2, b = p1 ++ p2 /\ r = p2 ++ p1.

(* 任意字符串输入，无额外约束 *)

(* cycpattern_check 函数的程序规约 *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Export string_bridge.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition problem_154_pre (a b : list Z) : Prop :=
  True.

Definition rot_index (shift j m : Z) : Z :=
  if (shift + j <? m)%Z then shift + j else shift + j - m.

Definition rotation_prefix
  (pos shift j : Z) (a b : list Z) : Prop :=
  forall k, 0 <= k < j ->
    Znth (pos + k) a 0 =
    Znth (rot_index shift k (Zlength b)) b 0.

Definition rotation_mismatch
  (pos shift j : Z) (a b : list Z) : Prop :=
  exists k, 0 <= k < j /\
    Znth (pos + k) a 0 <>
    Znth (rot_index shift k (Zlength b)) b 0.

Definition rotation_match_progress
  (pos shift j ok : Z) (a b : list Z) : Prop :=
  (ok = 1 -> rotation_prefix pos shift j a b) /\
  (ok = 0 -> rotation_mismatch pos shift j a b).

Definition rotation_match_at_spec
  (pos shift : Z) (a b : list Z) : Prop :=
  0 <= pos /\
  0 <= shift < Zlength b /\
  pos + Zlength b <= Zlength a /\
  rotation_prefix pos shift (Zlength b) a b.

Definition rotation_shift_search
  (shift pos found : Z) (a b : list Z) : Prop :=
  (found = 1 ->
    exists p, 0 <= p < pos /\ rotation_match_at_spec p shift a b) /\
  (found = 0 ->
    forall p, 0 <= p < pos -> ~ rotation_match_at_spec p shift a b).

Definition rotation_shift_has_match
  (shift : Z) (a b : list Z) : Prop :=
  exists p, 0 <= p /\ p + Zlength b <= Zlength a /\
    rotation_match_at_spec p shift a b.

Definition rotation_any_search
  (shift found : Z) (a b : list Z) : Prop :=
  (found = 1 ->
    exists s, 0 <= s < shift /\ rotation_shift_has_match s a b) /\
  (found = 0 ->
    forall s, 0 <= s < shift -> ~ rotation_shift_has_match s a b).

Definition rotation_any_match (a b : list Z) : Prop :=
  Zlength b = 0 \/
  exists s, 0 <= s < Zlength b /\ rotation_shift_has_match s a b.

Definition is_substring_z (sub main : list Z) : Prop :=
  exists prefix suffix, main = (prefix ++ sub ++ suffix)%list.

Definition is_rotation_z (r b : list Z) : Prop :=
  exists p1 p2, b = (p1 ++ p2)%list /\ r = (p2 ++ p1)%list.

Definition problem_154_spec (a b : list Z) (output : Z) : Prop :=
  let la := list_ascii_of_string (string_of_list a) in
  let lb := list_ascii_of_string (string_of_list b) in
  bool_of output = true <-> exists b', is_rotation_of b' lb /\ is_substring b' la.

Definition rotation_bytes (shift : Z) (b : list Z) : list Z :=
  sublist shift (Zlength b) b ++ sublist 0 shift b.

(* Helper lemmas migrated from the old proof, with names aligned to the input spec. *)
Lemma list_ascii_of_string_string_of_list_154 : forall l,
  list_ascii_of_string (string_of_list l) = map ascii_of l.
Proof.
  induction l as [|c rest IH]; simpl; [reflexivity|].
  rewrite IH.
  reflexivity.
Qed.
Lemma Zlength_map_154 : forall {A B : Type} (f : A -> B) (l : list A),
  Zlength (map f l) = Zlength l.
Proof.
  intros A B f l.
  repeat rewrite Zlength_correct.
  rewrite map_length.
  reflexivity.
Qed.

Lemma Znth_map_154 : forall {A B : Type} (f : A -> B) l i da db,
  0 <= i < Zlength l ->
  Znth i (map f l) db = f (Znth i l da).
Proof.
  intros A B f l i da db Hi.
  unfold Znth.
  transitivity (nth (Z.to_nat i) (map f l) (f da)).
  - apply nth_indep.
    rewrite map_length.
    rewrite Zlength_correct in Hi.
    lia.
  - apply map_nth.
Qed.

Lemma ascii_of_inj_154 : forall x y,
  0 <= x < 256 ->
  0 <= y < 256 ->
  ascii_of x = ascii_of y ->
  x = y.
Proof.
  intros x y Hx Hy H.
  apply f_equal with (f := nat_of_ascii) in H.
  unfold ascii_of in H.
  rewrite !nat_ascii_embedding in H by lia.
  apply f_equal with (f := Z.of_nat) in H.
  rewrite !Z2Nat.id in H by lia.
  exact H.
Qed.

Lemma map_sublist_154 : forall {A B : Type} (f : A -> B) lo hi (l : list A) (da : A) (db : B),
  0 <= lo ->
  lo <= hi ->
  hi <= Zlength l ->
  map f (sublist lo hi l) = sublist lo hi (map f l).
Proof.
  intros A B f lo hi l da db Hlo Hle Hhi.
  apply (proj2 (@list_eq_ext B
    (map f (sublist lo hi l))
    (sublist lo hi (map f l))
    db)).
  split.
  - rewrite Zlength_map_154.
    rewrite Zlength_sublist by lia.
    rewrite Zlength_sublist by (rewrite Zlength_map_154; lia).
    lia.
  - intros k Hk.
    rewrite Zlength_map_154 in Hk.
    rewrite Zlength_sublist in Hk by lia.
    rewrite (@Znth_map_154 A B f (sublist lo hi l) k da db)
      by (rewrite Zlength_sublist by lia; lia).
    rewrite !Znth_sublist by (rewrite ?Zlength_map_154; lia).
    rewrite (@Znth_map_154 A B f l (k + lo) da db) by lia.
    reflexivity.
Qed.

Lemma rotation_bytes_length : forall shift b,
  0 <= shift <= Zlength b ->
  Zlength (rotation_bytes shift b) = Zlength b.
Proof.
  intros shift b Hshift.
  unfold rotation_bytes.
  rewrite Zlength_app.
  rewrite !Zlength_sublist by lia.
  lia.
Qed.

Lemma Znth_rotation_bytes : forall shift b k,
  0 <= shift <= Zlength b ->
  0 <= k < Zlength b ->
  Znth k (rotation_bytes shift b) 0 =
  Znth (rot_index shift k (Zlength b)) b 0.
Proof.
  intros shift b k Hshift Hk.
  unfold rotation_bytes, rot_index.
  destruct (Z.ltb_spec (shift + k) (Zlength b)) as [Hlt | Hge].
  - rewrite app_Znth1 by (rewrite Zlength_sublist by lia; lia).
    rewrite Znth_sublist by lia.
    replace (k + shift) with (shift + k) by lia.
    reflexivity.
  - rewrite app_Znth2 by (rewrite Zlength_sublist by lia; lia).
    rewrite Zlength_sublist by lia.
    rewrite Znth_sublist by lia.
    replace (k - (Zlength b - shift) + 0) with (shift + k - Zlength b) by lia.
    reflexivity.
Qed.

Lemma rotation_match_segment_eq : forall a b pos shift,
  rotation_match_at_spec pos shift a b ->
  sublist pos (pos + Zlength b) a = rotation_bytes shift b.
Proof.
  intros a b pos shift [Hpos [Hshift [Hbound Hprefix]]].
  unfold rotation_prefix in Hprefix.
  apply (proj2 (@list_eq_ext Z
    (sublist pos (pos + Zlength b) a)
    (rotation_bytes shift b)
    0)).
  split.
  - rewrite Zlength_sublist by lia.
    rewrite rotation_bytes_length by lia.
    lia.
  - intros k Hk.
    rewrite Zlength_sublist in Hk by lia.
    rewrite Znth_sublist by lia.
    rewrite Znth_rotation_bytes by lia.
    replace (k + pos) with (pos + k) by lia.
    apply Hprefix.
    lia.
Qed.

Lemma rotation_match_at_spec_to_spec_exists : forall a b pos shift,
  rotation_match_at_spec pos shift a b ->
  exists b',
    is_rotation_of b' (map ascii_of b) /\
    is_substring b' (map ascii_of a).
Proof.
  intros a b pos shift Hmatch.
  destruct Hmatch as [Hpos [Hshift [Hbound Hprefix]]].
  exists (map ascii_of (rotation_bytes shift b)).
  split.
  - unfold is_rotation_of.
    exists (map ascii_of (sublist 0 shift b)).
    exists (map ascii_of (sublist shift (Zlength b) b)).
    split.
    + rewrite <- map_app.
      f_equal.
      assert (Hb_split :
        sublist 0 (Zlength b) b =
        (sublist 0 shift b ++ sublist shift (Zlength b) b)%list).
      {
        refine (sublist_split 0 (Zlength b) shift b _ _).
        - split; [lia | exact (proj1 Hshift)].
        - split; [apply Z.lt_le_incl; exact (proj2 Hshift) | rewrite Zlength_correct; reflexivity].
      }
      rewrite sublist_self in Hb_split by reflexivity.
      exact Hb_split.
    + unfold rotation_bytes.
      rewrite map_app.
      reflexivity.
  - unfold is_substring.
    exists (map ascii_of (sublist 0 pos a)).
    exists (map ascii_of (sublist (pos + Zlength b) (Zlength a) a)).
    pose proof (rotation_match_segment_eq a b pos shift
      (conj Hpos (conj Hshift (conj Hbound Hprefix)))) as Hseg.
    assert (Ha_split :
      a = ((sublist 0 pos a ++
          sublist pos (pos + Zlength b) a) ++
          sublist (pos + Zlength b) (Zlength a) a)%list).
    {
      assert (Hsplit1 :
        sublist 0 (Zlength a) a =
        (sublist 0 (pos + Zlength b) a ++
         sublist (pos + Zlength b) (Zlength a) a)%list).
      {
        refine (sublist_split 0 (Zlength a) (pos + Zlength b) a _ _).
        - split; lia.
        - split; [lia | rewrite Zlength_correct; reflexivity].
      }
      assert (Hsplit2 :
        sublist 0 (pos + Zlength b) a =
        (sublist 0 pos a ++ sublist pos (pos + Zlength b) a)%list).
      {
        refine (sublist_split 0 (pos + Zlength b) pos a _ _).
        - split; lia.
        - split.
          + pose proof (Zlength_nonneg b); lia.
          + exact Hbound.
      }
      rewrite sublist_self in Hsplit1 by reflexivity.
      rewrite Hsplit2 in Hsplit1.
      exact Hsplit1.
    }
    rewrite Ha_split at 1.
    rewrite Hseg at 1.
    rewrite !map_app.
    rewrite app_assoc.
    reflexivity.
Qed.

Lemma ascii_range_sublist_154 : forall l lo hi,
  ascii_range l ->
  0 <= lo ->
  lo <= hi ->
  hi <= Zlength l ->
  ascii_range (sublist lo hi l).
Proof.
  unfold ascii_range.
  intros l lo hi Hrange Hlo Hle Hhi i Hi.
  rewrite Zlength_sublist in Hi by lia.
  rewrite Znth_sublist by lia.
  apply Hrange.
  lia.
Qed.

Lemma ascii_range_rotation_bytes_154 : forall shift b,
  ascii_range b ->
  0 <= shift <= Zlength b ->
  ascii_range (rotation_bytes shift b).
Proof.
  unfold ascii_range.
  intros shift b Hrange Hshift i Hi.
  rewrite rotation_bytes_length in Hi by lia.
  rewrite Znth_rotation_bytes by lia.
  apply Hrange.
  unfold rot_index.
  destruct (Z.ltb_spec (shift + i) (Zlength b)); lia.
Qed.

Lemma map_ascii_eq_list_eq_154 : forall l1 l2,
  ascii_range l1 ->
  ascii_range l2 ->
  Zlength l1 = Zlength l2 ->
  map ascii_of l1 = map ascii_of l2 ->
  l1 = l2.
Proof.
  intros l1 l2 Hrange1 Hrange2 Hlen Hmap.
  apply (proj2 (@list_eq_ext Z l1 l2 0)).
  split; [exact Hlen |].
  intros k Hk.
  pose proof (proj1 (@list_eq_ext ascii
    (map ascii_of l1) (map ascii_of l2) (ascii_of 0)) Hmap) as [_ Hnth].
  assert (Hkmap : 0 <= k < Zlength (map ascii_of l1)).
  { rewrite Zlength_map_154. exact Hk. }
  specialize (Hnth k Hkmap).
  rewrite (@Znth_map_154 Z ascii ascii_of l1 k 0 (ascii_of 0)) in Hnth by lia.
  rewrite (@Znth_map_154 Z ascii ascii_of l2 k 0 (ascii_of 0)) in Hnth by lia.
  apply ascii_of_inj_154; try (apply Hrange1; lia);
    try (apply Hrange2; lia).
  exact Hnth.
Qed.

Lemma rotation_segment_eq_to_match_at : forall a b pos shift,
  0 <= pos ->
  0 <= shift < Zlength b ->
  pos + Zlength b <= Zlength a ->
  sublist pos (pos + Zlength b) a = rotation_bytes shift b ->
  rotation_match_at_spec pos shift a b.
Proof.
  intros a b pos shift Hpos Hshift Hbound Hseg.
  split; [exact Hpos |].
  split; [exact Hshift |].
  split; [exact Hbound |].
  unfold rotation_prefix.
  intros k Hk.
  pose proof (proj1 (@list_eq_ext Z
    (sublist pos (pos + Zlength b) a)
    (rotation_bytes shift b)
    0) Hseg) as [_ Hnth].
  assert (Hkseg : 0 <= k < Zlength (sublist pos (pos + Zlength b) a)).
  { rewrite Zlength_sublist by lia. lia. }
  specialize (Hnth k Hkseg).
  rewrite Znth_sublist in Hnth by lia.
  rewrite Znth_rotation_bytes in Hnth by lia.
  replace (k + pos) with (pos + k) in Hnth by lia.
  exact Hnth.
Qed.

Lemma rotation_bytes_zero : forall b,
  rotation_bytes 0 b = b.
Proof.
  intros b.
  apply (proj2 (@list_eq_ext Z (rotation_bytes 0 b) b 0)).
  split.
  - rewrite rotation_bytes_length by (pose proof (Zlength_nonneg b); lia).
    reflexivity.
  - intros k Hk.
    rewrite rotation_bytes_length in Hk by (pose proof (Zlength_nonneg b); lia).
    rewrite Znth_rotation_bytes by (pose proof (Zlength_nonneg b); lia).
    unfold rot_index.
    destruct (Z.ltb_spec (0 + k) (Zlength b)); [replace (0 + k) with k by lia; reflexivity | lia].
Qed.

Lemma map_rotation_bytes_from_ascii_split : forall b p1 p2,
  map ascii_of b = (p1 ++ p2)%list ->
  map ascii_of (rotation_bytes (Zlength p1) b) = (p2 ++ p1)%list.
Proof.
  intros b p1 p2 Hsplit.
  assert (Hlen : Zlength b = Zlength (p1 ++ p2)).
  {
    pose proof (f_equal (@Zlength ascii) Hsplit) as H.
    rewrite Zlength_map_154 in H.
    exact H.
  }
  unfold rotation_bytes.
  rewrite map_app.
  rewrite (map_sublist_154 ascii_of (Zlength p1) (Zlength b) b 0 (ascii_of 0)).
  2:{ pose proof (Zlength_nonneg p1); lia. }
  2:{ rewrite Hlen, Zlength_app; pose proof (Zlength_nonneg p2); lia. }
  2:{ lia. }
  rewrite (map_sublist_154 ascii_of 0 (Zlength p1) b 0 (ascii_of 0)).
  2:{ lia. }
  2:{ pose proof (Zlength_nonneg p1); lia. }
  2:{ rewrite Hlen, Zlength_app; pose proof (Zlength_nonneg p2); lia. }
  rewrite Hsplit.
  replace (Zlength b) with (Zlength (p1 ++ p2)) by (symmetry; exact Hlen).
  assert (Htail :
    sublist (Zlength p1) (Zlength (p1 ++ p2)) (p1 ++ p2) = p2).
  {
    rewrite (sublist_split_app_r (Zlength p1) (Zlength (p1 ++ p2))
      (Zlength p1) p1 p2).
    - replace (Zlength p1 - Zlength p1) with 0 by lia.
      replace (Zlength (p1 ++ p2) - Zlength p1) with (Zlength p2)
        by (rewrite Zlength_app; lia).
      rewrite sublist_self by reflexivity.
      reflexivity.
    - reflexivity.
    - split; [reflexivity | rewrite Zlength_app; pose proof (Zlength_nonneg p2); lia].
  }
  rewrite Htail.
  rewrite sublist_app_exact1.
  reflexivity.
Qed.

Lemma substring_segment_map_eq_154 : forall a b' prefix suffix,
  map ascii_of a = (prefix ++ b' ++ suffix)%list ->
  map ascii_of (sublist (Zlength prefix) (Zlength prefix + Zlength b') a) = b'.
Proof.
  intros a b' prefix suffix Hsub.
  rewrite (map_sublist_154 ascii_of (Zlength prefix)
    (Zlength prefix + Zlength b') a 0 (ascii_of 0)).
  2:{ pose proof (Zlength_nonneg prefix); lia. }
  2:{ pose proof (Zlength_nonneg b'); lia. }
  2:{
    pose proof (f_equal (@Zlength ascii) Hsub) as Hlen.
    rewrite Zlength_map_154 in Hlen.
    rewrite Zlength_app in Hlen.
    rewrite Zlength_app in Hlen.
    pose proof (Zlength_nonneg suffix).
    lia.
  }
  rewrite Hsub.
  rewrite (sublist_split_app_r (Zlength prefix)
    (Zlength prefix + Zlength b') (Zlength prefix)
    prefix (b' ++ suffix)).
  - replace (Zlength prefix + Zlength b' - Zlength prefix)
      with (Zlength b') by lia.
    replace (Zlength prefix - Zlength prefix) with 0 by lia.
    rewrite sublist_app_exact1.
    reflexivity.
  - reflexivity.
  - split.
    + reflexivity.
    + pose proof (Zlength_nonneg b'); lia.
Qed.

Lemma rotation_any_match_to_spec_exists : forall a b,
  rotation_any_match a b ->
  exists b',
    is_rotation_of b' (map ascii_of b) /\
    is_substring b' (map ascii_of a).
Proof.
  intros a b [Hb_empty | [s [_ [p [_ [_ Hmatch]]]]]].
  - exists nil.
    assert (b = nil) by (apply Zlength_nil_inv; lia).
    subst b.
    split.
    + unfold is_rotation_of. exists nil, nil. simpl. auto.
    + unfold is_substring. exists nil, (map ascii_of a). simpl. reflexivity.
  - eapply rotation_match_at_spec_to_spec_exists.
    exact Hmatch.
Qed.

Lemma is_rotation_of_length_154 : forall r b,
  is_rotation_of r b ->
  List.length r = List.length b.
Proof.
  unfold is_rotation_of.
  intros r b [p1 [p2 [Hb Hr]]].
  subst.
  rewrite !app_length.
  lia.
Qed.

Lemma is_substring_length_154 : forall sub main,
  is_substring sub main ->
  (List.length sub <= List.length main)%nat.
Proof.
  unfold is_substring.
  intros sub main [prefix [suffix Hmain]].
  subst.
  rewrite !app_length.
  lia.
Qed.

Lemma problem_154_spec_true_of_any_match : forall a b,
  rotation_any_match a b ->
  problem_154_spec a b 1.
Proof.
  intros a b Hmatch.
  unfold problem_154_spec, problem_154_spec, bool_of.
  rewrite !list_ascii_of_string_string_of_list_154.
  simpl.
  split.
  - intros _.
    apply rotation_any_match_to_spec_exists.
    exact Hmatch.
  - intros _. reflexivity.
Qed.

Lemma spec_exists_to_rotation_any_match : forall a b,
  ascii_range a ->
  ascii_range b ->
  (exists b',
    is_rotation_of b' (map ascii_of b) /\
    is_substring b' (map ascii_of a)) ->
  rotation_any_match a b.
Proof.
  intros a b Hrange_a Hrange_b [b' [Hrot Hsub]].
  destruct (Z.eq_dec (Zlength b) 0) as [Hb_empty | Hb_nonempty].
  - left. exact Hb_empty.
  - right.
    unfold is_rotation_of in Hrot.
    unfold is_substring in Hsub.
    destruct Hrot as [p1 [p2 [Hb_split Hb'_eq]]].
    destruct Hsub as [prefix [suffix Hsub]].
    subst b'.
    set (brot := (p2 ++ p1)%list).
    assert (Hbrot_len : Zlength brot = Zlength b).
    {
      unfold brot.
      pose proof (f_equal (@Zlength ascii) Hb_split) as Hlen.
      rewrite Zlength_map_154 in Hlen.
      rewrite !Zlength_app in *.
      lia.
    }
    assert (Hpos : 0 <= Zlength prefix) by apply Zlength_nonneg.
    assert (Hbound : Zlength prefix + Zlength b <= Zlength a).
    {
      pose proof (f_equal (@Zlength ascii) Hsub) as Hlen.
      rewrite Zlength_map_154 in Hlen.
      unfold brot in Hlen.
      rewrite !Zlength_app in Hlen.
      unfold brot in Hbrot_len.
      rewrite !Zlength_app in Hbrot_len.
      pose proof (Zlength_nonneg suffix).
      lia.
    }
    destruct p2 as [| c p2_tail].
    + exists 0.
      split.
      { pose proof (Zlength_nonneg b); lia. }
      exists (Zlength prefix).
      assert (Hbrot_map : map ascii_of (rotation_bytes 0 b) = brot).
      {
        unfold brot.
        simpl.
        rewrite app_nil_r in Hb_split.
        rewrite <- Hb_split.
        rewrite rotation_bytes_zero.
        reflexivity.
      }
      assert (Hseg_map :
        map ascii_of (sublist (Zlength prefix)
          (Zlength prefix + Zlength b) a) = brot).
      {
        replace (Zlength prefix + Zlength b)
          with (Zlength prefix + Zlength brot) by lia.
        apply (substring_segment_map_eq_154 a brot prefix suffix).
        exact Hsub.
      }
      assert (Hseg :
        sublist (Zlength prefix) (Zlength prefix + Zlength b) a =
        rotation_bytes 0 b).
      {
        apply map_ascii_eq_list_eq_154.
        - eapply ascii_range_sublist_154.
          + exact Hrange_a.
          + exact Hpos.
          + pose proof (Zlength_nonneg b); lia.
          + exact Hbound.
        - apply ascii_range_rotation_bytes_154.
          + exact Hrange_b.
          + pose proof (Zlength_nonneg b); lia.
        - rewrite Zlength_sublist by (pose proof (Zlength_nonneg b); lia).
          rewrite rotation_bytes_length by (pose proof (Zlength_nonneg b); lia).
          lia.
        - rewrite Hseg_map. symmetry. exact Hbrot_map.
      }
      split; [exact Hpos |].
      split; [exact Hbound |].
      apply rotation_segment_eq_to_match_at.
      * exact Hpos.
      * split; [lia | pose proof (Zlength_nonneg b); lia].
      * exact Hbound.
      * exact Hseg.
    + exists (Zlength p1).
      assert (Hp2_pos : 0 < Zlength (c :: p2_tail)).
      { rewrite Zlength_correct. simpl. lia. }
      split.
      {
        split; [apply Zlength_nonneg |].
        pose proof (f_equal (@Zlength ascii) Hb_split) as Hlen.
        rewrite Zlength_map_154 in Hlen.
        rewrite Zlength_app in Hlen.
        lia.
      }
      exists (Zlength prefix).
      assert (Hrot_map :
        map ascii_of (rotation_bytes (Zlength p1) b) = brot).
      {
        unfold brot.
        apply map_rotation_bytes_from_ascii_split.
        exact Hb_split.
      }
      assert (Hseg_map :
        map ascii_of (sublist (Zlength prefix)
          (Zlength prefix + Zlength b) a) = brot).
      {
        replace (Zlength prefix + Zlength b)
          with (Zlength prefix + Zlength brot) by lia.
        apply (substring_segment_map_eq_154 a brot prefix suffix).
        exact Hsub.
      }
      assert (Hseg :
        sublist (Zlength prefix) (Zlength prefix + Zlength b) a =
        rotation_bytes (Zlength p1) b).
      {
        apply map_ascii_eq_list_eq_154.
        - eapply ascii_range_sublist_154.
          + exact Hrange_a.
          + exact Hpos.
          + pose proof (Zlength_nonneg b); lia.
          + exact Hbound.
        - apply ascii_range_rotation_bytes_154.
          + exact Hrange_b.
          + split; [apply Zlength_nonneg |].
            pose proof (f_equal (@Zlength ascii) Hb_split) as Hlen.
            rewrite Zlength_map_154 in Hlen.
            rewrite Zlength_app in Hlen.
            lia.
        - rewrite Zlength_sublist by (pose proof (Zlength_nonneg b); lia).
          rewrite rotation_bytes_length.
          + lia.
          + split; [apply Zlength_nonneg |].
            pose proof (f_equal (@Zlength ascii) Hb_split) as Hlen.
            rewrite Zlength_map_154 in Hlen.
            rewrite Zlength_app in Hlen.
            lia.
        - rewrite Hseg_map. symmetry. exact Hrot_map.
      }
      split; [exact Hpos |].
      split; [exact Hbound |].
      apply rotation_segment_eq_to_match_at.
      * exact Hpos.
      * split; [apply Zlength_nonneg |].
        pose proof (f_equal (@Zlength ascii) Hb_split) as Hlen.
        rewrite Zlength_map_154 in Hlen.
        rewrite Zlength_app in Hlen.
        lia.
      * exact Hbound.
      * exact Hseg.
Qed.

Lemma problem_154_spec_false_of_no_any_match : forall a b,
  ascii_range a ->
  ascii_range b ->
  ~ rotation_any_match a b ->
  problem_154_spec a b 0.
Proof.
  intros a b Hrange_a Hrange_b Hnone.
  unfold problem_154_spec, problem_154_spec, bool_of.
  rewrite !list_ascii_of_string_string_of_list_154.
  simpl.
  split.
  - intros H; discriminate.
  - intros Hex.
    exfalso.
    apply Hnone.
    eapply spec_exists_to_rotation_any_match; eauto.
Qed.

Lemma problem_154_spec_false_too_long : forall a b,
  Zlength a < Zlength b ->
  problem_154_spec a b 0.
Proof.
  intros a b Hlen.
  unfold problem_154_spec, problem_154_spec, bool_of.
  rewrite !list_ascii_of_string_string_of_list_154.
  simpl.
  split.
  - intros H; discriminate.
  - intros [b' [Hrot Hsub]].
    pose proof (is_rotation_of_length_154 _ _ Hrot) as Hrot_len.
    pose proof (is_substring_length_154 _ _ Hsub) as Hsub_len.
    rewrite !map_length in Hrot_len, Hsub_len.
    rewrite !Zlength_correct in Hlen.
    lia.
Qed.

Lemma rotation_match_progress_init : forall pos shift a b,
  rotation_match_progress pos shift 0 1 a b.
Proof.
  unfold rotation_match_progress, rotation_prefix, rotation_mismatch.
  intros. split.
  - intros _ k Hk. lia.
  - intros H; discriminate.
Qed.

Lemma rotation_match_progress_step_same : forall pos shift j a b,
  0 <= j ->
  rotation_match_progress pos shift j 1 a b ->
  Znth (pos + j) a 0 =
    Znth (rot_index shift j (Zlength b)) b 0 ->
  rotation_match_progress pos shift (j + 1) 1 a b.
Proof.
  unfold rotation_match_progress, rotation_prefix, rotation_mismatch.
  intros pos shift j a b Hj [Hprefix _] Heq.
  split.
  - intros _ k Hk.
    destruct (Z.eq_dec k j) as [-> | Hne].
    + exact Heq.
    + apply Hprefix; lia.
  - intros H; discriminate.
Qed.

Lemma rotation_match_progress_step_keep_mismatch : forall pos shift j a b,
  0 <= j ->
  rotation_match_progress pos shift j 0 a b ->
  rotation_match_progress pos shift (j + 1) 0 a b.
Proof.
  unfold rotation_match_progress, rotation_prefix, rotation_mismatch.
  intros pos shift j a b Hj [_ Hmis].
  split.
  - intros H; discriminate.
  - intros _. destruct (Hmis eq_refl) as [k [Hk Hneq]].
    exists k. split; [lia | exact Hneq].
Qed.

Lemma rotation_match_progress_step_new_mismatch : forall pos shift j a b,
  0 <= j ->
  Znth (pos + j) a 0 <>
    Znth (rot_index shift j (Zlength b)) b 0 ->
  rotation_match_progress pos shift (j + 1) 0 a b.
Proof.
  unfold rotation_match_progress, rotation_prefix, rotation_mismatch.
  intros pos shift j a b Hj Hneq.
  split.
  - intros H; discriminate.
  - intros _. exists j. split; [lia | exact Hneq].
Qed.

Lemma rotation_match_at_from_progress : forall pos shift a b,
  0 <= pos ->
  0 <= shift < Zlength b ->
  pos + Zlength b <= Zlength a ->
  rotation_match_progress pos shift (Zlength b) 1 a b ->
  rotation_match_at_spec pos shift a b.
Proof.
  intros pos shift a b Hpos Hshift Hbound [Hprefix _].
  split; [exact Hpos |].
  split; [exact Hshift |].
  split; [exact Hbound |].
  apply Hprefix. reflexivity.
Qed.

Lemma not_rotation_match_at_from_progress : forall pos shift a b,
  rotation_match_progress pos shift (Zlength b) 0 a b ->
  ~ rotation_match_at_spec pos shift a b.
Proof.
  unfold rotation_match_at_spec, rotation_match_progress,
    rotation_prefix, rotation_mismatch.
  intros pos shift a b [_ Hmis] [_ [_ [_ Hprefix]]].
  destruct (Hmis eq_refl) as [k [Hk Hneq]].
  apply Hneq.
  apply Hprefix.
  exact Hk.
Qed.

Lemma rotation_shift_search_init : forall shift a b,
  rotation_shift_search shift 0 0 a b.
Proof.
  unfold rotation_shift_search.
  intros. split.
  - intros H; discriminate.
  - intros _ p Hp. lia.
Qed.

Lemma rotation_any_search_init : forall a b,
  rotation_any_search 0 0 a b.
Proof.
  unfold rotation_any_search.
  intros. split.
  - intros H; discriminate.
  - intros _ s Hs. lia.
Qed.

Lemma rotation_shift_search_step_hit : forall shift pos found a b,
  0 <= pos ->
  rotation_shift_search shift pos found a b ->
  rotation_match_at_spec pos shift a b ->
  rotation_shift_search shift (pos + 1) 1 a b.
Proof.
  unfold rotation_shift_search.
  intros shift pos found a b Hpos [Hfound _] Hmatch.
  split.
  - intros _. exists pos. split; [lia | exact Hmatch].
  - intros H; discriminate.
Qed.

Lemma rotation_shift_search_step_miss_zero : forall shift pos a b,
  0 <= pos ->
  rotation_shift_search shift pos 0 a b ->
  ~ rotation_match_at_spec pos shift a b ->
  rotation_shift_search shift (pos + 1) 0 a b.
Proof.
  unfold rotation_shift_search.
  intros shift pos a b Hpos [_ Hnone] Hmiss.
  split.
  - intros H; discriminate.
  - intros _ p Hp.
    destruct (Z.eq_dec p pos) as [-> | Hne].
    + exact Hmiss.
    + apply (Hnone eq_refl). lia.
Qed.

Lemma rotation_shift_search_step_miss_one : forall shift pos a b,
  0 <= pos ->
  rotation_shift_search shift pos 1 a b ->
  rotation_shift_search shift (pos + 1) 1 a b.
Proof.
  unfold rotation_shift_search.
  intros shift pos a b Hpos [Hfound _].
  split.
  - intros _. destruct (Hfound eq_refl) as [p [Hp Hmatch]].
    exists p. split; [lia | exact Hmatch].
  - intros H; discriminate.
Qed.

Lemma rotation_shift_search_final_hit : forall shift pos a b,
  rotation_shift_search shift pos 1 a b ->
  rotation_shift_has_match shift a b.
Proof.
  unfold rotation_shift_search, rotation_shift_has_match, rotation_match_at_spec.
  intros shift pos a b [Hfound _].
  destruct (Hfound eq_refl) as [p [_ Hmatch]].
  destruct Hmatch as [Hpos [Hshift [Hbound Hprefix]]].
  exists p.
  split; [exact Hpos |].
  split; [exact Hbound |].
  split; [exact Hpos |].
  split; [exact Hshift |].
  split; [exact Hbound | exact Hprefix].
Qed.

Lemma rotation_shift_search_final_miss : forall shift pos a b,
  pos = Zlength a - Zlength b + 1 ->
  rotation_shift_search shift pos 0 a b ->
  ~ rotation_shift_has_match shift a b.
Proof.
  unfold rotation_shift_search, rotation_shift_has_match.
  intros shift pos a b Hpos_eq [_ Hnone] [p [Hp0 [Hbound Hmatch]]].
  subst pos.
  apply (Hnone eq_refl p).
  - lia.
  - exact Hmatch.
Qed.

Lemma rotation_any_search_step_hit : forall shift found a b,
  0 <= shift ->
  rotation_any_search shift found a b ->
  rotation_shift_has_match shift a b ->
  rotation_any_search (shift + 1) 1 a b.
Proof.
  unfold rotation_any_search.
  intros shift found a b Hshift [Hfound _] Hmatch.
  split.
  - intros _. exists shift. split; [lia | exact Hmatch].
  - intros H; discriminate.
Qed.

Lemma rotation_any_search_step_miss_zero : forall shift a b,
  0 <= shift ->
  rotation_any_search shift 0 a b ->
  ~ rotation_shift_has_match shift a b ->
  rotation_any_search (shift + 1) 0 a b.
Proof.
  unfold rotation_any_search.
  intros shift a b Hshift [_ Hnone] Hmiss.
  split.
  - intros H; discriminate.
  - intros _ s Hs.
    destruct (Z.eq_dec s shift) as [-> | Hne].
    + exact Hmiss.
    + apply (Hnone eq_refl). lia.
Qed.

Lemma rotation_any_search_step_miss_one : forall shift a b,
  0 <= shift ->
  rotation_any_search shift 1 a b ->
  rotation_any_search (shift + 1) 1 a b.
Proof.
  unfold rotation_any_search.
  intros shift a b Hshift [Hfound _].
  split.
  - intros _. destruct (Hfound eq_refl) as [s [Hs Hmatch]].
    exists s. split; [lia | exact Hmatch].
  - intros H; discriminate.
Qed.

Lemma rotation_any_search_final_hit : forall shift a b,
  rotation_any_search shift 1 a b ->
  rotation_any_match a b.
Proof.
  unfold rotation_any_search, rotation_any_match.
  intros shift a b [Hfound _].
  right.
  destruct (Hfound eq_refl) as [s [[Hs0 Hslt] Hmatch]].
  exists s.
  destruct Hmatch as [p [Hp0 [Hbound Hmatch_at]]].
  destruct Hmatch_at as [Hpos [Hshift [Hbound_at Hprefix]]].
  split; [lia |].
  exists p. split; [exact Hp0 |].
  split; [exact Hbound |].
  split; [exact Hpos |].
  split; [exact Hshift |].
  split; [exact Hbound_at | exact Hprefix].
Qed.

Lemma rotation_any_search_final_miss : forall shift a b,
  0 < Zlength b ->
  shift = Zlength b ->
  rotation_any_search shift 0 a b ->
  ~ rotation_any_match a b.
Proof.
  unfold rotation_any_search, rotation_any_match.
  intros shift a b Hb Hshift [_ Hnone] [Hempty | [s [Hs Hmatch]]].
  - lia.
  - subst shift.
    apply (Hnone eq_refl s Hs).
    exact Hmatch.
Qed.

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
From SimpleC.EE.CAV.verify_20260605_080838v_ex_hamming_distance Require Import ex_hamming_distance_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import ex_hamming_distance.
Local Open Scope sac.

Lemma ex_hamming_distance_spec_bound :
  forall a b : list Z,
    Zlength a = Zlength b ->
    0 <= ex_hamming_distance_spec a b <= Zlength a.
Proof.
  intros a.
  induction a as [| x xs IH]; intros b Hlen.
  - destruct b as [| y ys].
    + rewrite Zlength_nil. simpl. lia.
    + rewrite Zlength_nil. simpl. lia.
  - destruct b as [| y ys].
    + rewrite Zlength_cons. simpl.
      split.
      * lia.
      * assert (0 <= Zlength xs) by apply Zlength_nonneg.
        lia.
    + rewrite !Zlength_cons in Hlen.
      assert (Htail : Zlength xs = Zlength ys) by lia.
      specialize (IH ys Htail).
      simpl.
      destruct IH as [IHlo IHhi].
      destruct (Z.eqb x y).
      * rewrite Zlength_cons.
        assert (0 <= Zlength xs) by apply Zlength_nonneg.
        lia.
      * rewrite Zlength_cons.
        assert (0 <= Zlength xs) by apply Zlength_nonneg.
        lia.
Qed.

Lemma sublist_zero_succ :
  forall (l : list Z) (i : Z),
    0 <= i < Zlength l ->
    sublist 0 (i + 1) l = sublist 0 i l ++ Znth i l 0 :: nil.
Proof.
  intros l i Hi.
  rewrite (sublist_split 0 (i + 1) i l); try lia.
  apply f_equal.
  apply sublist_single.
  exact Hi.
Qed.

Lemma cstring_nonzero_index_lt :
  forall (l : list Z) (n i : Z),
    Zlength l = n ->
    0 <= i <= n ->
    Znth i (l ++ 0 :: nil) 0 <> 0 ->
    i < n.
Proof.
  intros l n i Hlen Hrange Hnz.
  destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
  - exact Hlt.
  - assert (i = n) by lia.
    subst i.
    rewrite <- Hlen in Hnz.
    rewrite app_Znth2 in Hnz.
    2: lia.
    replace (Zlength l - Zlength l) with 0 in Hnz by lia.
    simpl in Hnz.
    contradiction Hnz.
    reflexivity.
Qed.

Lemma cstring_zero_index_eq_len :
  forall (l : list Z) (n i : Z),
    Zlength l = n ->
    0 <= i <= n ->
    Znth i (l ++ 0 :: nil) 0 = 0 ->
    (forall k : Z, 0 <= k < n -> Znth k l 0 <> 0) ->
    i = n.
Proof.
  intros l n i Hlen Hrange Hz Hnz.
  destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
  - specialize (Hnz i).
    assert (Znth i l 0 <> 0) by (apply Hnz; lia).
    rewrite app_Znth1 in Hz by (rewrite Hlen; lia).
    contradiction.
  - lia.
Qed.

Lemma ex_hamming_distance_spec_snoc :
  forall a b x y,
    Zlength a = Zlength b ->
    ex_hamming_distance_spec (a ++ x :: nil) (b ++ y :: nil) =
    ex_hamming_distance_spec a b + (if Z.eqb x y then 0 else 1).
Proof.
  intros a.
  induction a as [| xa xs IH]; intros b x y Hlen.
  - destruct b as [| yb ys].
    + simpl. destruct (Z.eqb x y); lia.
    + rewrite Zlength_nil, Zlength_cons in Hlen.
      exfalso.
      assert (0 <= Zlength ys) by apply Zlength_nonneg.
      lia.
  - destruct b as [| yb ys].
    + rewrite Zlength_cons, Zlength_nil in Hlen.
      exfalso.
      assert (0 <= Zlength xs) by apply Zlength_nonneg.
      lia.
    + rewrite !Zlength_cons in Hlen.
      assert (Htail : Zlength xs = Zlength ys) by lia.
      simpl.
      rewrite (IH ys x y Htail).
      lia.
Qed.

Lemma proof_of_ex_hamming_distance_safety_wit_5 : ex_hamming_distance_safety_wit_5.
Proof.
  pre_process.
  entailer!.
  - assert (Hsub_len : Zlength (sublist 0 i la) = Zlength (sublist 0 i lb)).
    {
      rewrite Zlength_sublist0.
      2: lia.
      rewrite Zlength_sublist0.
      2: {
        rewrite H7, <- H4.
        lia.
      }
      lia.
    }
    pose proof ex_hamming_distance_spec_bound (sublist 0 i la) (sublist 0 i lb) Hsub_len as Hbound.
    rewrite <- H5 in Hbound.
    lia.
  - assert (Hsub_len : Zlength (sublist 0 i la) = Zlength (sublist 0 i lb)).
    {
      rewrite Zlength_sublist0.
      2: lia.
      rewrite Zlength_sublist0.
      2: {
        rewrite H7, <- H4.
        lia.
      }
      lia.
    }
    pose proof ex_hamming_distance_spec_bound (sublist 0 i la) (sublist 0 i lb) Hsub_len as Hbound.
    rewrite <- H5 in Hbound.
    assert (Hlen_sub : Zlength (sublist 0 i la) = i).
    {
      rewrite Zlength_sublist0.
      2: lia.
      lia.
    }
    rewrite Hlen_sub in Hbound.
    lia.
Qed.

Lemma proof_of_ex_hamming_distance_entail_wit_1 : ex_hamming_distance_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  unfold ex_hamming_distance_pre in H7.
  rewrite H5, H6 in H7.
  lia.
Qed.

Lemma proof_of_ex_hamming_distance_entail_wit_2_1 : ex_hamming_distance_entail_wit_2_1.
Proof.
  pre_process.
  entailer!.
  assert (Hi_lt_na : i < na).
  {
    eapply cstring_nonzero_index_lt.
    - exact H6.
    - lia.
    - exact H0.
  }
  assert (Hi_lt_la : i < Zlength la) by (rewrite H6; lia).
  assert (Hi_lt_lb : i < Zlength lb) by (rewrite H7, <- H4; lia).
  assert (Hsuba : sublist 0 (i + 1) la = sublist 0 i la ++ Znth i la 0 :: nil).
  {
    apply sublist_zero_succ.
    split; [lia | exact Hi_lt_la].
  }
  assert (Hsubb : sublist 0 (i + 1) lb = sublist 0 i lb ++ Znth i lb 0 :: nil).
  {
    apply sublist_zero_succ.
    split; [lia | exact Hi_lt_lb].
  }
  assert (Hneq : Znth i la 0 <> Znth i lb 0).
  {
    rewrite app_Znth1 in H by (rewrite H6; lia).
    rewrite app_Znth1 in H by (rewrite H7; lia).
    exact H.
  }
  assert (Hsub_len : Zlength (sublist 0 i la) = Zlength (sublist 0 i lb)).
  {
    rewrite Zlength_sublist0.
    2: lia.
    rewrite Zlength_sublist0.
    2: {
      rewrite H7, <- H4.
      lia.
    }
    lia.
  }
  - rewrite Hsuba, Hsubb.
    rewrite ex_hamming_distance_spec_snoc by exact Hsub_len.
    rewrite H5.
    destruct (Z.eqb_spec (Znth i la 0) (Znth i lb 0)).
    + contradiction.
    + lia.
  - rewrite <- H4.
    assert (Hi_lt_na_branch : i < na).
    {
      eapply cstring_nonzero_index_lt.
      - exact H6.
      - lia.
      - exact H0.
    }
    lia.
  - assert (Hi_lt_na_branch : i < na).
    {
      eapply cstring_nonzero_index_lt.
      - exact H6.
      - lia.
      - exact H0.
    }
    lia.
Qed.

Lemma proof_of_ex_hamming_distance_entail_wit_2_2 : ex_hamming_distance_entail_wit_2_2.
Proof.
  pre_process.
  entailer!.
  assert (Hi_lt_na : i < na).
  {
    eapply cstring_nonzero_index_lt.
    - exact H6.
    - lia.
    - exact H0.
  }
  assert (Hi_lt_la : i < Zlength la) by (rewrite H6; lia).
  assert (Hi_lt_lb : i < Zlength lb) by (rewrite H7, <- H4; lia).
  assert (Hsuba : sublist 0 (i + 1) la = sublist 0 i la ++ Znth i la 0 :: nil).
  {
    apply sublist_zero_succ.
    split; [lia | exact Hi_lt_la].
  }
  assert (Hsubb : sublist 0 (i + 1) lb = sublist 0 i lb ++ Znth i lb 0 :: nil).
  {
    apply sublist_zero_succ.
    split; [lia | exact Hi_lt_lb].
  }
  assert (Heq : Znth i la 0 = Znth i lb 0).
  {
    rewrite app_Znth1 in H by (rewrite H6; lia).
    rewrite app_Znth1 in H by (rewrite H7; lia).
    exact H.
  }
  assert (Hsub_len : Zlength (sublist 0 i la) = Zlength (sublist 0 i lb)).
  {
    rewrite Zlength_sublist0.
    2: lia.
    rewrite Zlength_sublist0.
    2: {
      rewrite H7, <- H4.
      lia.
    }
    lia.
  }
  - rewrite Hsuba, Hsubb.
    rewrite ex_hamming_distance_spec_snoc by exact Hsub_len.
    rewrite H5.
    rewrite Heq.
    rewrite Z.eqb_refl.
    lia.
  - rewrite <- H4.
    assert (Hi_lt_na_branch : i < na).
    {
      eapply cstring_nonzero_index_lt.
      - exact H6.
      - lia.
      - exact H0.
    }
    lia.
  - assert (Hi_lt_na_branch : i < na).
    {
      eapply cstring_nonzero_index_lt.
      - exact H6.
      - lia.
      - exact H0.
    }
    lia.
Qed.

Lemma proof_of_ex_hamming_distance_return_wit_1 : ex_hamming_distance_return_wit_1.
Proof.
  pre_process.
  entailer!.
  assert (Hi_eq_na : i = na).
  {
    eapply cstring_zero_index_eq_len.
    - exact H5.
    - lia.
    - exact H.
    - exact H19.
  }
  assert (Hsuba : sublist 0 na la = la).
  {
    apply sublist_self.
    symmetry.
    exact H5.
  }
  assert (Hsubb : sublist 0 nb lb = lb).
  {
    apply sublist_self.
    symmetry.
    exact H6.
  }
  subst i.
  rewrite Hsuba in H4.
  assert (Hsubb_na : sublist 0 na lb = lb).
  {
    rewrite H3.
    exact Hsubb.
  }
  rewrite Hsubb_na in H4.
  exact H4.
Qed.

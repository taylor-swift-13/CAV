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
From SimpleC.EE.CAV.verify_20260607_082527_p122_add_elements Require Import p122_add_elements_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p122_add_elements.
Local Open Scope sac.

Lemma le99_equiv_lt100 : forall x, Z.leb x 99 = Z.ltb x 100.
Proof.
  intros.
  destruct (Z.leb x 99) eqn:H.
  - apply Z.leb_le in H. symmetry. apply Z.ltb_lt. lia.
  - apply Z.leb_gt in H. symmetry. apply Z.ltb_ge. lia.
Qed.

Lemma ge99_equiv_gt100 : forall x, Z.leb (-99) x = Z.ltb (-100) x.
Proof.
  intros.
  destruct (Z.leb (-99) x) eqn:H.
  - apply Z.leb_le in H. symmetry. apply Z.ltb_lt. lia.
  - apply Z.leb_gt in H. symmetry. apply Z.ltb_ge. lia.
Qed.

Lemma two_digit_cond_equiv : forall (x : Z),
  andb (Z.leb (-99) x) (Z.leb x 99) = is_at_most_two_digits x.
Proof.
  intros x.
  unfold is_at_most_two_digits.
  rewrite ge99_equiv_gt100.
  rewrite le99_equiv_lt100.
  reflexivity.
Qed.

Lemma fold_left_filter_single : forall x l,
  fold_left Z.add (filter is_at_most_two_digits (l ++ (x :: nil))) 0 =
  if is_at_most_two_digits x then fold_left Z.add (filter is_at_most_two_digits l) 0 + x
  else fold_left Z.add (filter is_at_most_two_digits l) 0.
Proof.
  intros x l.
  rewrite filter_app.
  rewrite fold_left_app.
  simpl.
  destruct (is_at_most_two_digits x).
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma sum_two_digit_upto_spec_eq : forall (k: Z) (lv: list Z),
  0 <= k ->
  k <= Zlength lv ->
  sum_two_digit_upto k lv = fold_left Z.add (filter is_at_most_two_digits (sublist 0 k lv)) 0.
Proof.
  intros k lv Hk Hlen.
  unfold sum_two_digit_upto.
  remember (Z.to_nat k) as n eqn:Hn.
  assert (Hk_eq : k = Z.of_nat n) by (apply Z2Nat.inj; try lia; rewrite Hn; symmetry; apply Nat2Z.id).
  subst k.
  induction n as [|n IH].
  - simpl. unfold sublist. simpl. reflexivity.
  - assert (Hstep :
      sum_two_digit_upto_nat (S n) lv =
      if is_at_most_two_digits (Znth (Z.of_nat n) lv 0)
      then sum_two_digit_upto_nat n lv + Znth (Z.of_nat n) lv 0
      else sum_two_digit_upto_nat n lv).
    { simpl. rewrite two_digit_cond_equiv. reflexivity. }
    rewrite Hstep.
    rewrite IH by lia.
    assert (Hn1 : Z.of_nat n + 1 <= Zlength lv).
    { replace (Z.of_nat n + 1) with (Z.of_nat (S n)) by lia. exact Hlen. }
    assert (Hn2 : Z.of_nat n < Zlength lv) by lia.
    assert (Hsplit: sublist 0 (Z.of_nat (S n)) lv = sublist 0 (Z.of_nat n) lv ++ (Znth (Z.of_nat n) lv 0 :: nil)).
    {
      replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
      assert (Hsub : sublist 0 (Z.of_nat n + 1) lv = sublist 0 (Z.of_nat n) lv ++ sublist (Z.of_nat n) (Z.of_nat n + 1) lv).
      { apply sublist_split; lia. }
      rewrite Hsub.
      f_equal.
      rewrite (sublist_single 0 (Z.of_nat n) lv) by lia.
      reflexivity.
    }
    rewrite Hsplit.
    rewrite filter_app.
    rewrite fold_left_app.
    simpl.
    destruct (is_at_most_two_digits (Znth (Z.of_nat n) lv 0)) eqn:Hd.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Lemma sum_two_digit_upto_step : forall i lv,
  0 <= i ->
  sum_two_digit_upto (i + 1) lv =
  if andb (Z.leb (-99) (Znth i lv 0)) (Z.leb (Znth i lv 0) 99)
  then sum_two_digit_upto i lv + Znth i lv 0
  else sum_two_digit_upto i lv.
Proof.
  intros.
  unfold sum_two_digit_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma proof_of_p122_add_elements_safety_wit_6 : p122_add_elements_safety_wit_6.
Proof.
  pre_process.
  unfold sum_two_digit_int_range in H8.
  assert (Hbound : INT_MIN <= s + Znth i lv 0 <= INT_MAX).
  {
    assert (Hconj := H8 i H9 H1).
    destruct Hconj as [_ Hpart2].
    rewrite <- H11 in Hpart2.
    exact Hpart2.
  }
  split_pures.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_p122_add_elements_entail_wit_1 : p122_add_elements_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_p122_add_elements_entail_wit_2_1 : p122_add_elements_entail_wit_2_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre arr_size_pre lv).
  - split_pures.
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; lia).
    all: dump_pre_spatial.
    assert (Hs : s = sum_two_digit_upto i lv) by assumption.
    assert (Hstep : sum_two_digit_upto (i + 1) lv =
      if andb (Z.leb (-99) (Znth i lv 0)) (Z.leb (Znth i lv 0) 99)
      then sum_two_digit_upto i lv + Znth i lv 0
      else sum_two_digit_upto i lv).
    { apply sum_two_digit_upto_step. lia. }
    assert (Hcond : andb (Z.leb (-99) (Znth i lv 0)) (Z.leb (Znth i lv 0) 99) = true).
    { apply andb_true_iff. split; apply Z.leb_le; lia. }
    rewrite Hstep.
    rewrite Hcond.
    rewrite Hs.
    reflexivity.
Qed.

Lemma proof_of_p122_add_elements_entail_wit_2_2 : p122_add_elements_entail_wit_2_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre arr_size_pre lv).
  - split_pures.
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; lia).
    all: dump_pre_spatial.
    assert (Hs : s = sum_two_digit_upto i lv) by assumption.
    assert (Hstep : sum_two_digit_upto (i + 1) lv =
      if andb (Z.leb (-99) (Znth i lv 0)) (Z.leb (Znth i lv 0) 99)
      then sum_two_digit_upto i lv + Znth i lv 0
      else sum_two_digit_upto i lv).
    { apply sum_two_digit_upto_step. lia. }
    assert (Hcond : andb (Z.leb (-99) (Znth i lv 0)) (Z.leb (Znth i lv 0) 99) = false).
    { apply andb_false_iff. left. apply Z.leb_gt. lia. }
    rewrite Hstep.
    rewrite Hcond.
    rewrite Hs.
    reflexivity.
Qed.

Lemma proof_of_p122_add_elements_entail_wit_2_3 : p122_add_elements_entail_wit_2_3.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre arr_size_pre lv).
  - split_pures.
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; lia).
    all: dump_pre_spatial.
    assert (Hs : s = sum_two_digit_upto i lv) by assumption.
    assert (Hstep : sum_two_digit_upto (i + 1) lv =
      if andb (Z.leb (-99) (Znth i lv 0)) (Z.leb (Znth i lv 0) 99)
      then sum_two_digit_upto i lv + Znth i lv 0
      else sum_two_digit_upto i lv).
    { apply sum_two_digit_upto_step. lia. }
    assert (Hcond : andb (Z.leb (-99) (Znth i lv 0)) (Z.leb (Znth i lv 0) 99) = false).
    { apply andb_false_iff. right. apply Z.leb_gt. lia. }
    rewrite Hstep.
    rewrite Hcond.
    rewrite Hs.
    reflexivity.
Qed.

Lemma proof_of_p122_add_elements_return_wit_1 : p122_add_elements_return_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre arr_size_pre lv).
  - dump_pre_spatial.
    assert (Hi : i = k_pre) by lia.
    subst i.
    match goal with
    | H : s = sum_two_digit_upto k_pre lv |- _ => rewrite H
    end.
    unfold problem_122_spec.
    apply sum_two_digit_upto_spec_eq; lia.
Qed.

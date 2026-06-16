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
From SimpleC.EE.CAV.verify_20260607_152224_p072_will_it_fly Require Import p072_will_it_fly_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p072_will_it_fly.

Lemma fold_left_Z_add_acc : forall (l : list Z) (acc : Z),
  fold_left (fun a x => a + x) l acc = acc + sum l.
Proof.
  induction l as [|a t IH]; intros acc.
  - simpl. unfold sum. simpl. ring.
  - simpl. rewrite IH. unfold sum. simpl. ring.
Qed.

Lemma sum_sublist_step : forall (lv : list Z) (i : Z),
  0 <= i < Zlength lv ->
  sum (sublist 0 (i + 1) lv) = sum (sublist 0 i lv) + Znth i lv 0.
Proof.
  intros lv i Hi.
  rewrite (sublist_split 0 (i + 1) i lv) by lia.
  rewrite (sublist_single 0 i lv) by lia.
  rewrite sum_app.
  unfold sum at 2. simpl. ring.
Qed.

Lemma Znth_rev_lem : forall (l : list Z) (k : Z),
  0 <= k < Zlength l ->
  Znth k (rev l) 0 = Znth (Zlength l - 1 - k) l 0.
Proof.
  intros l k Hk.
  unfold Znth.
  destruct (Z_lt_dec k 0). { lia. }
  destruct (Z_lt_dec (Zlength l - 1 - k) 0).
  { rewrite Zlength_correct in *. lia. }
  rewrite rev_nth by (rewrite Zlength_correct in Hk; lia).
  f_equal.
  rewrite Zlength_correct.
  rewrite Z2Nat.inj_sub by lia.
  rewrite Z2Nat.inj_sub by lia.
  rewrite Nat2Z.id.
  simpl (Z.to_nat 1).
  lia.
Qed.

Lemma mirror_to_rev : forall (lv : list Z),
  (forall k, 0 <= k < Zlength lv -> Znth k lv 0 = Znth (Zlength lv - 1 - k) lv 0) ->
  lv = rev lv.
Proof.
  intros lv Hmirror.
  rewrite (list_eq_ext lv (rev lv) 0).
  split.
  - rewrite !Zlength_correct. rewrite length_rev. reflexivity.
  - intros i Hi.
    rewrite Znth_rev_lem by exact Hi.
    apply Hmirror. exact Hi.
Qed.

Local Open Scope sac.

Lemma proof_of_p072_will_it_fly_safety_wit_7 : p072_will_it_fly_safety_wit_7.
Proof.
  pre_process.
  assert (Hwifr : will_it_fly_int_range lv) by eassumption.
  assert (Hqlen : q_size_pre = Zlength lv) by eassumption.
  assert (Hilen : i < q_size_pre) by eassumption.
  assert (Hs : s = sum (sublist 0 i lv)) by eassumption.
  pose proof (sum_sublist_step lv i ltac:(rewrite <- Hqlen; lia)) as Hstep.
  pose proof (Hwifr (i + 1) ltac:(rewrite <- Hqlen; lia)) as [Hlo Hhi].
  split_pures.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_p072_will_it_fly_entail_wit_1 : p072_will_it_fly_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_p072_will_it_fly_entail_wit_2 : p072_will_it_fly_entail_wit_2.
Proof.
  pre_process.
  assert (Hqlen : q_size_pre = Zlength lv) by eassumption.
  assert (Hs : s = sum (sublist 0 i lv)) by eassumption.
  assert (Hilt : i < q_size_pre) by eassumption.
  assert (Hmirror : forall k0 : Z, (0 <= k0 /\ k0 < i) ->
    Znth k0 lv 0 = Znth (q_size_pre - 1 - k0) lv 0) by eassumption.
  assert (Hnew : Znth i lv 0 = Znth (q_size_pre - 1 - i) lv 0) by eassumption.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    all: try eassumption.
    all: try exact I.
    all: try (intros k0 [Hk1 Hk2];
              destruct (Z.eq_dec k0 i) as [Heq | Hne];
              [ subst k0; exact Hnew | apply Hmirror; split; lia ]).
    all: try (rewrite sum_sublist_step by (rewrite <- Hqlen; lia); lia).
Qed.

Lemma proof_of_p072_will_it_fly_return_wit_1 : p072_will_it_fly_return_wit_1.
Proof.
  pre_process.
  assert (Heqi : i = q_size_pre) by lia.
  subst i.
  split_pure_spatial.
  { cancel. }
  { split_pures; dump_pre_spatial.
    assert (Hqlen : q_size_pre = Zlength lv) by eassumption.
    assert (Hs : s = sum (sublist 0 q_size_pre lv)) by eassumption.
    assert (Hsle : s <= w_pre) by eassumption.
    assert (Hmirror : forall k0 : Z, (0 <= k0 /\ k0 < q_size_pre) ->
      Znth k0 lv 0 = Znth (q_size_pre - 1 - k0) lv 0) by eassumption.
    rewrite (sublist_self lv q_size_pre Hqlen) in Hs.
    unfold problem_72_spec.
    split.
    { right. reflexivity. }
    split.
    { intros _.
      split.
      { apply mirror_to_rev.
        intros k Hk.
        rewrite <- Hqlen.
        apply Hmirror. split; lia. }
      { rewrite fold_left_Z_add_acc. lia. } }
    { intros _. reflexivity. } }
Qed.

Lemma proof_of_p072_will_it_fly_return_wit_2 : p072_will_it_fly_return_wit_2.
Proof.
  pre_process.
  assert (Heqi : i = q_size_pre) by lia.
  subst i.
  split_pure_spatial.
  { cancel. }
  { split_pures; dump_pre_spatial.
    assert (Hqlen : q_size_pre = Zlength lv) by eassumption.
    assert (Hs : s = sum (sublist 0 q_size_pre lv)) by eassumption.
    assert (Hgt : s > w_pre) by eassumption.
    rewrite (sublist_self lv q_size_pre Hqlen) in Hs.
    unfold problem_72_spec.
    split.
    { left. reflexivity. }
    split.
    { intro Heq0. discriminate Heq0. }
    { intro Hconj.
      destruct Hconj as [_ Hfold].
      rewrite fold_left_Z_add_acc in Hfold.
      lia. } }
Qed.

Lemma proof_of_p072_will_it_fly_return_wit_3 : p072_will_it_fly_return_wit_3.
Proof.
  pre_process.
  split_pure_spatial.
  { cancel. }
  { split_pures; dump_pre_spatial.
    assert (Hqlen : q_size_pre = Zlength lv) by eassumption.
    assert (Hilt : i < q_size_pre) by eassumption.
    assert (Hige : 0 <= i) by eassumption.
    assert (Hneq : Znth i lv 0 <> Znth (q_size_pre - 1 - i) lv 0) by eassumption.
    unfold problem_72_spec.
    split.
    { left. reflexivity. }
    split.
    { intro Heq0. discriminate Heq0. }
    { intro Hconj.
      destruct Hconj as [Hrev _].
      exfalso.
      apply Hneq.
      rewrite Hqlen.
      rewrite <- (Znth_rev_lem lv i ltac:(rewrite <- Hqlen; lia)).
      rewrite <- Hrev.
      reflexivity. } }
Qed.

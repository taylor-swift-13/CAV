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
From SimpleC.EE.CAV.ground_truth_p072_will_it_fly Require Import p072_will_it_fly_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import List.
Require Import ZArith.
From AUXLib Require Import ListLib.
Require Import Coq.micromega.Lia.

Import naive_C_Rules.
Require Import p072_will_it_fly.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p072_will_it_fly.v so public contract files expose definitions only. *)

Lemma fold_left_Zadd_sum : forall l acc,
  fold_left Z.add l acc = acc + sum l.
Proof.
  induction l; intros; simpl.
  - lia.
  - rewrite IHl. simpl. lia.
Qed.
Lemma fold_left_Zadd_0_sum : forall l,
  fold_left Z.add l 0 = sum l.
Proof.
  intros. rewrite fold_left_Zadd_sum. lia.
Qed.
Lemma mirror_all_rev : forall q,
  mirror_all q ->
  q = rev q.
Proof.
  intros q Hmirror.
  apply nth_ext with (d := 0) (d' := 0).
  - rewrite length_rev. reflexivity.
  - intros n Hn.
    rewrite rev_nth by lia.
    specialize (Hmirror (Z.of_nat n)).
    unfold Znth in Hmirror.
    rewrite Nat2Z.id in Hmirror.
    replace (Z.to_nat (Zlength q - 1 - Z.of_nat n))
      with (length q - S n)%nat in Hmirror.
    + apply Hmirror. rewrite Zlength_correct. lia.
    + rewrite Zlength_correct. lia.
Qed.
Lemma rev_mirror_all : forall q,
  q = rev q ->
  mirror_all q.
Proof.
  intros q Hrev k Hk.
  unfold Znth.
  assert (Hk_nat : (Z.to_nat k < length q)%nat).
  { rewrite Zlength_correct in Hk. lia. }
  rewrite Hrev at 1.
  rewrite rev_nth by exact Hk_nat.
  replace (length q - S (Z.to_nat k))%nat
    with (Z.to_nat (Zlength q - 1 - k)).
  - reflexivity.
  - rewrite Zlength_correct.
    apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite Nat2Z.inj_sub by lia.
    rewrite Nat2Z.inj_succ.
    rewrite Z2Nat.id by lia.
    lia.
Qed.
Lemma problem_72_spec_false : forall q w,
  ~ (q = rev q /\ fold_left (fun acc x => acc + x) q 0 <= w) ->
  problem_72_spec q w 0.
Proof.
  intros q w Hfalse.
  unfold problem_72_spec, problem_72_spec.
  split.
  - left. reflexivity.
  - simpl.
    split; intro H; [discriminate | contradiction].
Qed.
Lemma sum_sublist_0 : forall l,
  sum (sublist 0 0 l) = 0.
Proof.
  intros. rewrite Zsublist_nil by lia. reflexivity.
Qed.
Lemma sum_sublist_snoc : forall l i,
  0 <= i < Zlength l ->
  sum (sublist 0 i l) + Znth i l 0 = sum (sublist 0 (i + 1) l).
Proof.
  intros l i Hi.
  rewrite (sublist_split 0 (i + 1) i l)
    by (try rewrite <- Zlength_correct; lia).
  rewrite (sublist_single 0 i l) by lia.
  rewrite sum_app. simpl. lia.
Qed.
Lemma mirror_prefix_extend : forall q n i,
  n = Zlength q ->
  0 <= i < n ->
  (forall k, 0 <= k < i -> Znth k q 0 = Znth (n - 1 - k) q 0) ->
  Znth i q 0 = Znth (n - 1 - i) q 0 ->
  forall k, 0 <= k < i + 1 -> Znth k q 0 = Znth (n - 1 - k) q 0.
Proof.
  intros q n i Hn Hi Hprefix Hi_eq k Hk.
  destruct (Z.eq_dec k i) as [-> | Hneq].
  - exact Hi_eq.
  - apply Hprefix. lia.
Qed.
Lemma mirror_prefix_mismatch_spec_false : forall q w n i,
  n = Zlength q ->
  0 <= i < n ->
  (forall k, 0 <= k < i -> Znth k q 0 = Znth (n - 1 - k) q 0) ->
  Znth i q 0 <> Znth (n - 1 - i) q 0 ->
  problem_72_spec q w 0.
Proof.
  intros q w n i Hn Hi _ Hneq.
  apply problem_72_spec_false.
  intros [Hrev _].
  pose proof (rev_mirror_all q Hrev) as Hmirror.
  specialize (Hmirror i).
  rewrite <- Hn in Hmirror.
  apply Hneq. apply Hmirror. lia.
Qed.
Lemma mirror_prefix_full : forall q n i,
  n = Zlength q ->
  i >= n ->
  (forall k, 0 <= k < i -> Znth k q 0 = Znth (n - 1 - k) q 0) ->
  mirror_all q.
Proof.
  intros q n i Hn Hi Hprefix k Hk.
  unfold mirror_all.
  rewrite <- Hn in Hk.
  rewrite <- Hn.
  apply Hprefix. lia.
Qed.
Lemma problem_72_spec_weight_false : forall q w,
  mirror_all q ->
  sum q > w ->
  problem_72_spec q w 0.
Proof.
  intros q w Hmirror Hgt.
  apply problem_72_spec_false.
  rewrite fold_left_Zadd_0_sum.
  intros [_ Hsum]. lia.
Qed.
Lemma problem_72_spec_true : forall q w,
  mirror_all q ->
  sum q <= w ->
  problem_72_spec q w 1.
Proof.
  intros q w Hmirror Hsum.
  unfold problem_72_spec, problem_72_spec.
  split.
  - right. reflexivity.
  - simpl.
    split.
    * intros _.
      split.
      -- apply mirror_all_rev. exact Hmirror.
      -- rewrite fold_left_Zadd_0_sum. exact Hsum.
    * intros _.
      reflexivity.
Qed.


Lemma proof_of_p072_will_it_fly_safety_wit_7 : p072_will_it_fly_safety_wit_7.
Proof.
  pre_process.
  subst s.
  rewrite sum_sublist_snoc by lia.
  entailer!;
  match goal with
  | H: will_it_fly_int_range _ |- _ =>
      unfold will_it_fly_int_range in H;
      specialize (H (i + 1)); lia
  end.
Qed.

Lemma proof_of_p072_will_it_fly_entail_wit_1 : p072_will_it_fly_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_p072_will_it_fly_entail_wit_2 : p072_will_it_fly_entail_wit_2.
Proof.
  pre_process.
  subst s.
  rewrite sum_sublist_snoc by lia.
  entailer!.
  apply mirror_prefix_extend with (n := q_size_pre); auto; lia.
Qed.

Lemma proof_of_p072_will_it_fly_return_wit_1 : p072_will_it_fly_return_wit_1.
Proof.
  pre_process.
  assert (Hsfull: s = sum lv).
  {
    match goal with
    | Hs: s = sum (sublist 0 i lv) |- _ => rewrite Hs
    end.
    replace i with (Zlength lv) by lia.
    rewrite sublist_self by reflexivity.
    reflexivity.
  }
  entailer!.
  apply problem_72_spec_true.
  - apply mirror_prefix_full with (n := q_size_pre) (i := i); auto; lia.
  - lia.
Qed.

Lemma proof_of_p072_will_it_fly_return_wit_2 : p072_will_it_fly_return_wit_2.
Proof.
  pre_process.
  assert (Hsum_gt: sum lv > w_pre).
  {
    rewrite H8 in H.
    replace i with (Zlength lv) in H by lia.
    rewrite sublist_self in H by reflexivity.
    exact H.
  }
  entailer!.
  apply problem_72_spec_weight_false.
  - apply mirror_prefix_full with (n := q_size_pre) (i := i); auto; lia.
  - lia.
Qed.

Lemma proof_of_p072_will_it_fly_return_wit_3 : p072_will_it_fly_return_wit_3.
Proof.
  pre_process.
  entailer!.
  apply mirror_prefix_mismatch_spec_false with (n := q_size_pre) (i := i); auto; lia.
Qed.

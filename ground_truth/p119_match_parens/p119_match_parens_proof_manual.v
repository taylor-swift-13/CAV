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
From SimpleC.EE.CAV.ground_truth_p119_match_parens Require Import p119_match_parens_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.

Import naive_C_Rules.
Require Import p119_match_parens.
Local Open Scope sac.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope list_scope.

(* Proof helpers moved from p119_match_parens.v so public contract files expose definitions only. *)

Lemma paren_level_upto_0 : forall l,
  paren_level_upto 0 l = 0.
Proof.
  reflexivity.
Qed.
Lemma paren_good_prefix_flag_0 : forall l,
  paren_good_prefix_flag 0 l = 1.
Proof.
  reflexivity.
Qed.
Lemma paren_delta_bound : forall x,
  -1 <= paren_delta x <= 1.
Proof.
  unfold paren_delta.
  intro x.
  repeat match goal with
  | |- context[Z.eqb ?a ?b] => destruct (Z.eqb_spec a b); simpl
  end; lia.
Qed.
Lemma paren_level_upto_step : forall i l,
  0 <= i ->
  paren_level_upto (i + 1) l =
  paren_level_upto i l + paren_delta (Znth i l 0).
Proof.
  intros i l Hi.
  unfold paren_level_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.
Lemma paren_level_upto_step_open : forall i l,
  0 <= i ->
  Znth i l 0 = 40 ->
  paren_level_upto (i + 1) l = paren_level_upto i l + 1.
Proof.
  intros i l Hi Hx.
  rewrite paren_level_upto_step by lia.
  unfold paren_delta.
  rewrite Hx, Z.eqb_refl.
  reflexivity.
Qed.
Lemma paren_level_upto_step_close : forall i l,
  0 <= i ->
  Znth i l 0 = 41 ->
  paren_level_upto (i + 1) l = paren_level_upto i l - 1.
Proof.
  intros i l Hi Hx.
  rewrite paren_level_upto_step by lia.
  unfold paren_delta.
  rewrite Hx.
  replace (Z.eqb 41 40) with false by reflexivity.
  rewrite Z.eqb_refl.
  lia.
Qed.
Lemma paren_level_upto_step_other : forall i l,
  0 <= i ->
  Znth i l 0 <> 40 ->
  Znth i l 0 <> 41 ->
  paren_level_upto (i + 1) l = paren_level_upto i l.
Proof.
  intros i l Hi H40 H41.
  rewrite paren_level_upto_step by lia.
  unfold paren_delta.
  replace (Z.eqb (Znth i l 0) 40) with false by
    (symmetry; apply Z.eqb_neq; lia).
  replace (Z.eqb (Znth i l 0) 41) with false by
    (symmetry; apply Z.eqb_neq; lia).
  lia.
Qed.
Lemma paren_good_prefix_flag_step_nonneg : forall i l level,
  0 <= i ->
  paren_good_prefix_flag i l = 1 ->
  level = paren_level_upto (i + 1) l ->
  0 <= level ->
  paren_good_prefix_flag (i + 1) l = 1.
Proof.
  intros i l level Hi Hflag Hlevel Hnonneg.
  unfold paren_good_prefix_flag in *.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  destruct (paren_good_prefix_bool_nat (Z.to_nat i) l); try discriminate.
  rewrite <- Hlevel.
  replace (Z.leb 0 level) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.
Lemma paren_good_prefix_flag_step_neg : forall i l level,
  0 <= i ->
  level = paren_level_upto (i + 1) l ->
  level < 0 ->
  paren_good_prefix_flag (i + 1) l = 0.
Proof.
  intros i l level Hi Hlevel Hneg.
  unfold paren_good_prefix_flag.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  rewrite <- Hlevel.
  replace (Z.leb 0 level) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (paren_good_prefix_bool_nat (Z.to_nat i) l); reflexivity.
Qed.
Lemma paren_good_prefix_flag_step_bad : forall i l,
  0 <= i ->
  paren_good_prefix_flag i l = 0 ->
  paren_good_prefix_flag (i + 1) l = 0.
Proof.
  intros i l Hi Hflag.
  unfold paren_good_prefix_flag in *.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  destruct (paren_good_prefix_bool_nat (Z.to_nat i) l); try discriminate.
  reflexivity.
Qed.
Lemma paren_good_prefix_flag_bool : forall i l,
  paren_good_prefix_flag i l = 0 \/ paren_good_prefix_flag i l = 1.
Proof.
  intros i l.
  unfold paren_good_prefix_flag.
  destruct (paren_good_prefix_bool_nat (Z.to_nat i) l); auto.
Qed.
Lemma Znth_app_left_119 : forall (l1 l2 : list Z) i d,
  0 <= i < Zlength l1 ->
  Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros l1 l2 i d Hi.
  unfold Znth.
  rewrite app_nth1.
  - reflexivity.
  - rewrite Zlength_correct in Hi.
    assert ((Z.to_nat i < Datatypes.length l1)%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
    lia.
Qed.
Lemma Znth_app_right_119 : forall (l1 l2 : list Z) i d,
  Zlength l1 <= i < Zlength l1 + Zlength l2 ->
  Znth i (l1 ++ l2) d = Znth (i - Zlength l1) l2 d.
Proof.
  intros l1 l2 i d Hi.
  unfold Znth.
  rewrite app_nth2.
  - replace (Datatypes.length l1) with (Z.to_nat (Zlength l1)).
    + pose proof (Zlength_nonneg l1).
      rewrite <- Z2Nat.inj_sub by lia.
      reflexivity.
    + rewrite Zlength_correct.
      apply Nat2Z.id.
  - rewrite Zlength_correct in Hi.
    assert ((Datatypes.length l1 <= Z.to_nat i)%nat).
    { apply Nat2Z.inj_le. rewrite Z2Nat.id by lia. lia. }
    lia.
Qed.
Lemma paren_level_bound : forall i l,
  0 <= i ->
  -i <= paren_level_upto i l <= i.
Proof.
  intros i l Hi.
  unfold paren_level_upto.
  remember (Z.to_nat i) as n eqn:Hn.
  assert (Hiz : i = Z.of_nat n) by lia.
  subst i.
  induction n as [| n IH]; simpl.
  - lia.
  - pose proof (paren_delta_bound (Znth (Z.of_nat n) l 0)).
    lia.
Qed.
Lemma paren_level_upto_nat_cons : forall n c rest,
  paren_level_upto_nat (S n) (c :: rest) =
  paren_delta c + paren_level_upto_nat n rest.
Proof.
  induction n as [| n IH]; intros c rest.
  - simpl. rewrite Z.add_0_r. reflexivity.
  - change (paren_level_upto_nat (S n) (c :: rest) +
            paren_delta (Znth (Z.of_nat (S n)) (c :: rest) 0) =
            paren_delta c + paren_level_upto_nat (S n) rest).
    rewrite IH.
    rewrite Znth_cons by lia.
    replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
    rewrite <- Z.add_assoc.
    reflexivity.
Qed.
Lemma paren_level_upto_cons_succ : forall c rest k,
  0 <= k ->
  paren_level_upto (k + 1) (c :: rest) =
  paren_delta c + paren_level_upto k rest.
Proof.
  intros c rest k Hk.
  unfold paren_level_upto.
  replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  rewrite paren_level_upto_nat_cons.
  reflexivity.
Qed.
Lemma paren_level_upto_Zlength_sum : forall l,
  paren_level_upto (Zlength l) l = paren_sum_list l.
Proof.
  induction l as [| c rest IH].
  - reflexivity.
  - rewrite Zlength_cons.
    unfold paren_level_upto.
    replace (Z.to_nat (Z.succ (Zlength rest))) with (S (Z.to_nat (Zlength rest))) by
      (pose proof (Zlength_nonneg rest); lia).
    rewrite paren_level_upto_nat_cons.
    fold (paren_level_upto (Zlength rest) rest).
    rewrite IH.
    reflexivity.
Qed.
Lemma paren_sum_list_app : forall l1 l2,
  paren_sum_list (l1 ++ l2) = paren_sum_list l1 + paren_sum_list l2.
Proof.
  induction l1 as [| c rest IH]; intros l2; simpl.
  - lia.
  - rewrite IH. lia.
Qed.
Lemma paren_total_app_comm : forall l1 l2,
  paren_level_upto (Zlength (l1 ++ l2)) (l1 ++ l2) =
  paren_level_upto (Zlength (l2 ++ l1)) (l2 ++ l1).
Proof.
  intros l1 l2.
  repeat rewrite paren_level_upto_Zlength_sum.
  repeat rewrite paren_sum_list_app.
  lia.
Qed.
Lemma check_parens_z_inner_true_level : forall l depth,
  0 <= depth ->
  check_parens_z_inner l depth = true ->
  depth + paren_level_upto (Zlength l) l = 0.
Proof.
  induction l as [| c rest IH]; intros depth Hdepth Hcheck.
  - simpl in Hcheck.
    apply Z.eqb_eq in Hcheck.
    unfold paren_level_upto; simpl.
    lia.
  - simpl in Hcheck.
    destruct (Z.eqb_spec c 40) as [Hopen | Hnopen].
    + specialize (IH (depth + 1) ltac:(lia) Hcheck).
      rewrite Zlength_cons.
      unfold paren_level_upto.
      replace (Z.to_nat (Z.succ (Zlength rest))) with
        (S (Z.to_nat (Zlength rest))) by (pose proof (Zlength_nonneg rest); lia).
      rewrite paren_level_upto_nat_cons.
      unfold paren_delta.
      rewrite Hopen, Z.eqb_refl.
      fold (paren_level_upto (Zlength rest) rest).
      lia.
    + destruct (Z.eqb_spec c 41) as [Hclose | Hnclose].
      * destruct (Z.eqb_spec depth 0); try discriminate.
        specialize (IH (depth - 1) ltac:(lia) Hcheck).
        rewrite Zlength_cons.
        unfold paren_level_upto.
        replace (Z.to_nat (Z.succ (Zlength rest))) with
          (S (Z.to_nat (Zlength rest))) by (pose proof (Zlength_nonneg rest); lia).
        rewrite paren_level_upto_nat_cons.
        unfold paren_delta.
        rewrite Hclose.
        replace (Z.eqb 41 40) with false by reflexivity.
        rewrite Z.eqb_refl.
        fold (paren_level_upto (Zlength rest) rest).
        lia.
      * specialize (IH depth Hdepth Hcheck).
        rewrite Zlength_cons.
        unfold paren_level_upto.
        replace (Z.to_nat (Z.succ (Zlength rest))) with
          (S (Z.to_nat (Zlength rest))) by (pose proof (Zlength_nonneg rest); lia).
        rewrite paren_level_upto_nat_cons.
        unfold paren_delta.
        replace (Z.eqb c 40) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (Z.eqb c 41) with false by (symmetry; apply Z.eqb_neq; lia).
        fold (paren_level_upto (Zlength rest) rest).
        lia.
Qed.
Lemma is_balanced_false_from_level : forall l,
  paren_level_upto (Zlength l) l <> 0 ->
  is_balanced l = false.
Proof.
  intros l Hlevel.
  unfold is_balanced.
  destruct (check_parens_z_inner l 0) eqn:Hcheck; auto.
  pose proof (check_parens_z_inner_true_level l 0 ltac:(lia) Hcheck).
  lia.
Qed.
Lemma check_parens_z_inner_true_prefix : forall l depth,
  0 <= depth ->
  check_parens_z_inner l depth = true ->
  forall k, 0 <= k < Zlength l ->
    0 <= depth + paren_level_upto (k + 1) l.
Proof.
  induction l as [| c rest IH]; intros depth Hdepth Hcheck k Hk.
  - rewrite Zlength_nil in Hk. lia.
  - simpl in Hcheck.
    destruct (Z.eqb_spec c 40) as [Hopen | Hnopen].
    + destruct (Z.eq_dec k 0) as [-> | Hk0].
      * replace (paren_level_upto (0 + 1) (c :: rest)) with 1.
        -- lia.
        -- replace (0 + 1) with 1 by lia.
           unfold paren_level_upto; simpl.
           unfold paren_delta. rewrite Hopen, Z.eqb_refl. lia.
      * assert (0 <= k - 1 < Zlength rest) by (rewrite Zlength_cons in Hk; lia).
        specialize (IH (depth + 1) ltac:(lia) Hcheck (k - 1) H).
        rewrite paren_level_upto_cons_succ by lia.
        unfold paren_delta.
        rewrite Hopen, Z.eqb_refl.
        replace (k - 1 + 1) with k in IH by lia.
        replace (k + 1 - 1) with k by lia.
        lia.
    + destruct (Z.eqb_spec c 41) as [Hclose | Hnclose].
      * destruct (Z.eqb_spec depth 0); try discriminate.
        destruct (Z.eq_dec k 0) as [-> | Hk0].
        -- replace (paren_level_upto (0 + 1) (c :: rest)) with (-1).
           ++ assert (1 <= depth) by lia. lia.
           ++ replace (0 + 1) with 1 by lia.
              unfold paren_level_upto; simpl.
              unfold paren_delta. rewrite Hclose.
              change (Znth 0 (c :: rest) 0) with c.
              replace (Z.eqb 41 40) with false by reflexivity.
              rewrite Z.eqb_refl. reflexivity.
        -- assert (0 <= k - 1 < Zlength rest) by (rewrite Zlength_cons in Hk; lia).
           specialize (IH (depth - 1) ltac:(lia) Hcheck (k - 1) H).
           rewrite paren_level_upto_cons_succ by lia.
           unfold paren_delta.
           rewrite Hclose.
           replace (Z.eqb 41 40) with false by reflexivity.
           rewrite Z.eqb_refl.
           replace (k - 1 + 1) with k in IH by lia.
           replace (k + 1 - 1) with k by lia.
           lia.
      * destruct (Z.eq_dec k 0) as [-> | Hk0].
        -- replace (paren_level_upto (0 + 1) (c :: rest)) with 0.
           ++ lia.
           ++ replace (0 + 1) with 1 by lia.
              unfold paren_level_upto; simpl.
              unfold paren_delta.
              change (Znth 0 (c :: rest) 0) with c.
              replace (Z.eqb c 40) with false by (symmetry; apply Z.eqb_neq; lia).
              replace (Z.eqb c 41) with false by (symmetry; apply Z.eqb_neq; lia).
              reflexivity.
        -- assert (0 <= k - 1 < Zlength rest) by (rewrite Zlength_cons in Hk; lia).
           specialize (IH depth Hdepth Hcheck (k - 1) H).
           rewrite paren_level_upto_cons_succ by lia.
           unfold paren_delta.
           replace (Z.eqb c 40) with false by (symmetry; apply Z.eqb_neq; lia).
           replace (Z.eqb c 41) with false by (symmetry; apply Z.eqb_neq; lia).
           replace (k - 1 + 1) with k in IH by lia.
           replace (k + 1 - 1) with k by lia.
           lia.
Qed.
Lemma paren_good_prefix_bool_nat_true_iff : forall n l,
  paren_good_prefix_bool_nat n l = true <->
  forall k, 0 <= k < Z.of_nat n -> 0 <= paren_level_upto (k + 1) l.
Proof.
  induction n as [| n IH]; intros l; simpl.
  - split.
    + intros _ k Hk. lia.
    + intros _. reflexivity.
  - rewrite andb_true_iff.
    rewrite IH.
    split.
    + intros [Hprefix Hlast] k Hk.
      destruct (Z_lt_ge_dec k (Z.of_nat n)).
      * apply Hprefix. lia.
      * assert (k = Z.of_nat n) by lia. subst k.
        apply Z.leb_le in Hlast. exact Hlast.
    + intros Hprefix.
      split.
      * intros k Hk. apply Hprefix. lia.
      * apply Z.leb_le. apply Hprefix. lia.
Qed.
Lemma check_parens_z_inner_true_from_scan : forall l depth,
  0 <= depth ->
  (forall k, 0 <= k < Zlength l ->
    0 <= depth + paren_level_upto (k + 1) l) ->
  depth + paren_level_upto (Zlength l) l = 0 ->
  check_parens_z_inner l depth = true.
Proof.
  induction l as [| c rest IH]; intros depth Hdepth Hprefix Hfinal.
  - rewrite Zlength_nil in Hfinal.
    rewrite paren_level_upto_0 in Hfinal.
    replace depth with 0 by lia.
    reflexivity.
  - simpl.
    pose proof (Hprefix 0 ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg rest); lia))
      as Hfirst.
    rewrite paren_level_upto_cons_succ in Hfirst by lia.
    replace (0 + 1 - 1) with 0 in Hfirst by lia.
    rewrite paren_level_upto_0 in Hfirst.
    destruct (Z.eqb_spec c 40) as [Hopen | Hnopen].
    + apply IH.
      * lia.
      * intros k Hk.
        specialize (Hprefix (k + 1)).
        rewrite paren_level_upto_cons_succ in Hprefix by lia.
        replace (k + 1 + 1 - 1) with (k + 1) in Hprefix by lia.
        specialize (Hprefix ltac:(rewrite Zlength_cons; lia)).
        unfold paren_delta in Hprefix. rewrite Hopen, Z.eqb_refl in Hprefix. lia.
      * rewrite Zlength_cons in Hfinal.
        replace (Z.succ (Zlength rest)) with (Zlength rest + 1) in Hfinal by lia.
        rewrite paren_level_upto_cons_succ in Hfinal by (pose proof (Zlength_nonneg rest); lia).
        replace (Z.succ (Zlength rest) - 1) with (Zlength rest) in Hfinal by lia.
        unfold paren_delta in Hfinal. rewrite Hopen, Z.eqb_refl in Hfinal. lia.
    + destruct (Z.eqb_spec c 41) as [Hclose | Hnclose].
      * assert (depth <> 0).
        { unfold paren_delta in Hfirst.
          rewrite Hclose in Hfirst.
          replace (Z.eqb 41 40) with false in Hfirst by reflexivity.
          rewrite Z.eqb_refl in Hfirst.
          lia. }
        replace (Z.eqb depth 0) with false by (symmetry; apply Z.eqb_neq; lia).
        apply IH.
        -- lia.
        -- intros k Hk.
           specialize (Hprefix (k + 1)).
           rewrite paren_level_upto_cons_succ in Hprefix by lia.
           replace (k + 1 + 1 - 1) with (k + 1) in Hprefix by lia.
           specialize (Hprefix ltac:(rewrite Zlength_cons; lia)).
           unfold paren_delta in Hprefix. rewrite Hclose in Hprefix.
           replace (Z.eqb 41 40) with false in Hprefix by reflexivity.
           rewrite Z.eqb_refl in Hprefix. lia.
        -- rewrite Zlength_cons in Hfinal.
           replace (Z.succ (Zlength rest)) with (Zlength rest + 1) in Hfinal by lia.
           rewrite paren_level_upto_cons_succ in Hfinal by (pose proof (Zlength_nonneg rest); lia).
           replace (Z.succ (Zlength rest) - 1) with (Zlength rest) in Hfinal by lia.
           unfold paren_delta in Hfinal. rewrite Hclose in Hfinal.
           replace (Z.eqb 41 40) with false in Hfinal by reflexivity.
           rewrite Z.eqb_refl in Hfinal. lia.
      * apply IH.
        -- lia.
        -- intros k Hk.
           specialize (Hprefix (k + 1)).
           rewrite paren_level_upto_cons_succ in Hprefix by lia.
           replace (k + 1 + 1 - 1) with (k + 1) in Hprefix by lia.
           specialize (Hprefix ltac:(rewrite Zlength_cons; lia)).
           unfold paren_delta in Hprefix.
           replace (Z.eqb c 40) with false in Hprefix by (symmetry; apply Z.eqb_neq; lia).
           replace (Z.eqb c 41) with false in Hprefix by (symmetry; apply Z.eqb_neq; lia).
           lia.
        -- rewrite Zlength_cons in Hfinal.
           replace (Z.succ (Zlength rest)) with (Zlength rest + 1) in Hfinal by lia.
           rewrite paren_level_upto_cons_succ in Hfinal by (pose proof (Zlength_nonneg rest); lia).
           replace (Z.succ (Zlength rest) - 1) with (Zlength rest) in Hfinal by lia.
           unfold paren_delta in Hfinal.
           replace (Z.eqb c 40) with false in Hfinal by (symmetry; apply Z.eqb_neq; lia).
           replace (Z.eqb c 41) with false in Hfinal by (symmetry; apply Z.eqb_neq; lia).
           lia.
Qed.
Lemma check_parens_z_true_from_scan : forall l,
  paren_level_upto (Zlength l) l = 0 ->
  paren_good_prefix_flag (Zlength l) l = 1 ->
  is_balanced l = true.
Proof.
  intros l Hlevel Hflag.
  unfold is_balanced.
  apply check_parens_z_inner_true_from_scan.
  - lia.
  - intros k Hk.
    unfold paren_good_prefix_flag in Hflag.
    destruct (paren_good_prefix_bool_nat (Z.to_nat (Zlength l)) l) eqn:Hb; try discriminate.
    pose proof (proj1 (paren_good_prefix_bool_nat_true_iff (Z.to_nat (Zlength l)) l) Hb) as Hprefix.
    apply Hprefix.
    rewrite Z2Nat.id by (pose proof (Zlength_nonneg l); lia).
    lia.
  - lia.
Qed.
Lemma is_balanced_false_from_flag : forall l,
  paren_level_upto (Zlength l) l = 0 ->
  paren_good_prefix_flag (Zlength l) l = 0 ->
  is_balanced l = false.
Proof.
  intros l Hlevel Hflag.
  destruct (is_balanced l) eqn:Hbal; auto.
  unfold is_balanced in Hbal.
  pose proof (check_parens_z_inner_true_prefix l 0 ltac:(lia) Hbal) as Hprefix.
  unfold paren_good_prefix_flag in Hflag.
  destruct (paren_good_prefix_bool_nat (Z.to_nat (Zlength l)) l) eqn:Hb; try discriminate.
  exfalso.
  assert (Htrue : paren_good_prefix_bool_nat (Z.to_nat (Zlength l)) l = true).
  {
    apply (proj2 (paren_good_prefix_bool_nat_true_iff (Z.to_nat (Zlength l)) l)).
    intros k Hk.
    apply Hprefix.
    rewrite Z2Nat.id in Hk by (pose proof (Zlength_nonneg l); lia).
    lia.
  }
  rewrite Hb in Htrue. discriminate.
Qed.
Lemma problem_119_pre_l1_char : forall l1 l2 i,
  problem_119_pre l1 l2 ->
  ascii_range l1 ->
  0 <= i < Zlength l1 ->
  Znth i l1 0 = 40 \/ Znth i l1 0 = 41.
Proof.
  intros l1 l2 i Hpre _ Hi.
  destruct Hpre as [Hpre1 _].
  apply Hpre1; lia.
Qed.
Lemma problem_119_pre_l2_char : forall l1 l2 i,
  problem_119_pre l1 l2 ->
  ascii_range l2 ->
  0 <= i < Zlength l2 ->
  Znth i l2 0 = 40 \/ Znth i l2 0 = 41.
Proof.
  intros l1 l2 i Hpre _ Hi.
  destruct Hpre as [_ Hpre2].
  apply Hpre2; lia.
Qed.
Lemma problem_119_pre_l1_nonzero : forall l1 l2 i,
  problem_119_pre l1 l2 ->
  0 <= i < Zlength l1 ->
  Znth i l1 0 <> 0.
Proof.
  intros l1 l2 i Hpre Hi.
  destruct Hpre as [Hpre1 _].
  pose proof (Hpre1 i Hi) as [Hc | Hc]; rewrite Hc; lia.
Qed.
Lemma problem_119_pre_l2_nonzero : forall l1 l2 i,
  problem_119_pre l1 l2 ->
  0 <= i < Zlength l2 ->
  Znth i l2 0 <> 0.
Proof.
  intros l1 l2 i Hpre Hi.
  destruct Hpre as [_ Hpre2].
  pose proof (Hpre2 i Hi) as [Hc | Hc]; rewrite Hc; lia.
Qed.
Lemma problem_119_spec_true_left : forall l1 l2,
  ascii_range l1 ->
  ascii_range l2 ->
  paren_level_upto (Zlength (l1 ++ l2)) (l1 ++ l2) = 0 ->
  paren_good_prefix_flag (Zlength (l1 ++ l2)) (l1 ++ l2) = 1 ->
  problem_119_spec l1 l2 1.
Proof.
  intros l1 l2 _ _ Hlevel Hflag.
  unfold problem_119_spec, bool_of.
  rewrite Z.eqb_refl.
  split.
  - intros _.
    left.
    apply check_parens_z_true_from_scan; auto.
  - intros _.
    reflexivity.
Qed.
Lemma problem_119_spec_true_right : forall l1 l2,
  ascii_range l1 ->
  ascii_range l2 ->
  paren_level_upto (Zlength (l2 ++ l1)) (l2 ++ l1) = 0 ->
  paren_good_prefix_flag (Zlength (l2 ++ l1)) (l2 ++ l1) = 1 ->
  problem_119_spec l1 l2 1.
Proof.
  intros l1 l2 _ _ Hlevel Hflag.
  unfold problem_119_spec, bool_of.
  rewrite Z.eqb_refl.
  split.
  - intros _.
    right.
    apply check_parens_z_true_from_scan; auto.
  - intros _.
    reflexivity.
Qed.
Lemma problem_119_spec_false_from_level : forall l1 l2,
  ascii_range l1 ->
  ascii_range l2 ->
  paren_level_upto (Zlength (l1 ++ l2)) (l1 ++ l2) <> 0 ->
  problem_119_spec l1 l2 0.
Proof.
  intros l1 l2 _ _ Hlevel.
  unfold problem_119_spec, bool_of.
  replace (Z.eqb 0 1) with false by reflexivity.
  split.
  - discriminate.
  - intros [Hleft | Hright].
    + rewrite (is_balanced_false_from_level (l1 ++ l2)) in Hleft by exact Hlevel.
      discriminate.
    + assert (Hlevel2 : paren_level_upto (Zlength (l2 ++ l1)) (l2 ++ l1) <> 0).
      { rewrite <- paren_total_app_comm. exact Hlevel. }
      rewrite (is_balanced_false_from_level (l2 ++ l1)) in Hright by exact Hlevel2.
      discriminate.
Qed.
Lemma problem_119_spec_false_from_flags : forall l1 l2,
  ascii_range l1 ->
  ascii_range l2 ->
  paren_level_upto (Zlength (l1 ++ l2)) (l1 ++ l2) = 0 ->
  paren_good_prefix_flag (Zlength (l1 ++ l2)) (l1 ++ l2) = 0 ->
  paren_good_prefix_flag (Zlength (l2 ++ l1)) (l2 ++ l1) = 0 ->
  problem_119_spec l1 l2 0.
Proof.
  intros l1 l2 _ _ Hlevel Hflag12 Hflag21.
  unfold problem_119_spec, bool_of.
  replace (Z.eqb 0 1) with false by reflexivity.
  split.
  - discriminate.
  - intros [Hleft | Hright].
    + rewrite (is_balanced_false_from_flag (l1 ++ l2)) in Hleft by eauto.
      discriminate.
    + assert (Hlevel2 : paren_level_upto (Zlength (l2 ++ l1)) (l2 ++ l1) = 0).
      { rewrite <- paren_total_app_comm. exact Hlevel. }
      rewrite (is_balanced_false_from_flag (l2 ++ l1)) in Hright by eauto.
      discriminate.
Qed.


Ltac mp_base :=
  pre_process; subst; entailer!;
  try rewrite paren_level_upto_0;
  try rewrite paren_good_prefix_flag_0;
  try lia.

Ltac normalize_input_char :=
  repeat match goal with
  | Hlen : Zlength ?l = ?n,
    Hi : ?i < ?n,
    Hc : Znth ?i (app ?l (cons 0 nil)) 0 = ?v |- _ =>
      rewrite Znth_app_left_119 in Hc by lia
  | Hlen : Zlength ?l = ?n,
    Hi : ?i < ?n,
    Hc : Znth ?i (app ?l (cons 0 nil)) 0 <> ?v |- _ =>
      rewrite Znth_app_left_119 in Hc by lia
  end.

Ltac rewrite_concat_left l1 l2 i :=
  rewrite (Znth_app_left_119 l1 l2 i 0) by lia.

Ltac rewrite_concat_right l1 l2 i :=
  rewrite (Znth_app_right_119 l1 l2 i 0) by lia;
  replace (i - Zlength l1) with (i - Zlength l1) by lia.

Ltac prove_flag_nonneg idx lst newlevel can :=
  let Hflag := fresh "Hflag" in
  destruct (paren_good_prefix_flag_bool idx lst) as [Hflag | Hflag];
  rewrite <- can in Hflag; subst;
  [ rewrite paren_good_prefix_flag_step_bad by lia; reflexivity
  | eapply paren_good_prefix_flag_step_nonneg; try eassumption; lia ].

Ltac step_open_common idx lst Hchar :=
  rewrite (paren_level_upto_step_open idx lst) by (try lia; exact Hchar).

Ltac step_close_common idx lst Hchar :=
  rewrite (paren_level_upto_step_close idx lst) by (try lia; exact Hchar).

Ltac step_other_common idx lst H40 H41 :=
  rewrite (paren_level_upto_step_other idx lst) by (try lia; exact H40 || exact H41).

Ltac finish_negative_flag idx lst :=
  eapply paren_good_prefix_flag_step_neg; try eassumption; lia.

Ltac solve_119_nonzero :=
  intros k Hk;
  match goal with
  | Hpre : problem_119_pre ?l1 ?l2 |- Znth k ?l1 0 <> 0 =>
      eapply problem_119_pre_l1_nonzero; eauto
  | Hpre : problem_119_pre ?l1 ?l2 |- Znth k ?l2 0 <> 0 =>
      eapply problem_119_pre_l2_nonzero; eauto
  end.

Ltac solve_l1_step :=
  pre_process; subst; normalize_input_char; entailer!;
  repeat match goal with
  | H : Znth ?i ?l 0 = 40 |- context[paren_level_upto (?i + 1) ?l] =>
      step_open_common i l H
  | H : Znth ?i ?l 0 = 41 |- context[paren_level_upto (?i + 1) ?l] =>
      step_close_common i l H
  | H40 : Znth ?i ?l 0 <> 40, H41 : Znth ?i ?l 0 <> 41 |- context[paren_level_upto (?i + 1) ?l] =>
      step_other_common i l H40 H41
  end;
  try match goal with
  | |- context[paren_good_prefix_flag (?i + 1) ?l] =>
      first [ finish_negative_flag i l
            | prove_flag_nonneg i l (paren_level_upto (i + 1) l) ltac:(match goal with H: ?can = paren_good_prefix_flag i l |- _ => exact H end) ]
  end;
  try lia.

Lemma proof_of_p119_match_parens_entail_wit_1 : p119_match_parens_entail_wit_1.
Proof.
  unfold p119_match_parens_entail_wit_1.
  intros.
  mp_base.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_2_1 : p119_match_parens_entail_wit_2_1.
Proof.
  unfold p119_match_parens_entail_wit_2_1.
  intros.
  pre_process; subst.
  assert (Hchar_concat : Znth i (l1 ++ l2) 0 = 40).
  {
    rewrite Znth_app_left_119 by lia.
    match goal with
    | H : Znth i (app l1 (cons 0 nil)) 0 = 40 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat); lia).
  symmetry.
  eapply (paren_good_prefix_flag_step_neg i (l1 ++ l2)
    (paren_level_upto i (l1 ++ l2) + 1)).
  - lia.
  - rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat). lia.
  - lia.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_2_2 : p119_match_parens_entail_wit_2_2.
Proof.
  unfold p119_match_parens_entail_wit_2_2.
  intros.
  pre_process; subst.
  assert (Hchar_concat : Znth i (l1 ++ l2) 0 = 41).
  {
    rewrite Znth_app_left_119 by lia.
    match goal with
    | H : Znth i (app l1 (cons 0 nil)) 0 = 41 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat); lia).
  symmetry.
  eapply (paren_good_prefix_flag_step_neg i (l1 ++ l2)
    (paren_level_upto i (l1 ++ l2) - 1)).
  - lia.
  - rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat). lia.
  - lia.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_2_3 : p119_match_parens_entail_wit_2_3.
Proof.
  unfold p119_match_parens_entail_wit_2_3.
  intros.
  pre_process; subst.
  pose proof (problem_119_pre_l1_char l1 l2 i ltac:(eassumption) ltac:(eassumption) ltac:(lia)) as [Hc | Hc].
  - assert (Znth i (l1 ++ cons 0 nil) 0 = 40) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
  - assert (Znth i (l1 ++ cons 0 nil) 0 = 41) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_2_4 : p119_match_parens_entail_wit_2_4.
Proof.
  unfold p119_match_parens_entail_wit_2_4.
  intros.
  pre_process; subst.
  pose proof (problem_119_pre_l1_char l1 l2 i ltac:(eassumption) ltac:(eassumption) ltac:(lia)) as [Hc | Hc].
  - assert (Znth i (l1 ++ cons 0 nil) 0 = 40) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
  - assert (Znth i (l1 ++ cons 0 nil) 0 = 41) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_2_5 : p119_match_parens_entail_wit_2_5.
Proof.
  unfold p119_match_parens_entail_wit_2_5.
  intros.
  pre_process; subst.
  assert (Hchar_concat : Znth i (l1 ++ l2) 0 = 41).
  {
    rewrite Znth_app_left_119 by lia.
    match goal with
    | H : Znth i (app l1 (cons 0 nil)) 0 = 41 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat); lia).
  destruct (paren_good_prefix_flag_bool i (l1 ++ l2)) as [Hflag | Hflag].
  - rewrite Hflag.
    symmetry. apply paren_good_prefix_flag_step_bad; lia.
  - rewrite Hflag.
    symmetry.
    eapply (paren_good_prefix_flag_step_nonneg i (l1 ++ l2)
      (paren_level_upto i (l1 ++ l2) - 1)).
    + lia.
    + exact Hflag.
    + rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat). lia.
    + lia.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_2_6 : p119_match_parens_entail_wit_2_6.
Proof.
  unfold p119_match_parens_entail_wit_2_6.
  intros.
  pre_process; subst.
  assert (Hchar_concat : Znth i (l1 ++ l2) 0 = 40).
  {
    rewrite Znth_app_left_119 by lia.
    match goal with
    | H : Znth i (app l1 (cons 0 nil)) 0 = 40 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat); lia).
  destruct (paren_good_prefix_flag_bool i (l1 ++ l2)) as [Hflag | Hflag].
  - rewrite Hflag.
    symmetry. apply paren_good_prefix_flag_step_bad; lia.
  - rewrite Hflag.
    symmetry.
    eapply (paren_good_prefix_flag_step_nonneg i (l1 ++ l2)
      (paren_level_upto i (l1 ++ l2) + 1)).
    + lia.
    + exact Hflag.
    + rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat). lia.
    + lia.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_3 : p119_match_parens_entail_wit_3.
Proof.
  unfold p119_match_parens_entail_wit_3.
  intros.
  pre_process; subst.
  assert (i = Zlength l1) by lia.
  subst i.
  replace (Zlength l1 + 0) with (Zlength l1) by lia.
  entailer!.
Qed.

Lemma proof_of_p119_match_parens_entail_wit_4_1 : p119_match_parens_entail_wit_4_1.
Proof.
  unfold p119_match_parens_entail_wit_4_1.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth (Zlength l1 + i) (l1 ++ l2) 0 = 40).
  {
    rewrite Znth_app_right_119 by lia.
    replace (Zlength l1 + i - Zlength l1) with i by lia.
    match goal with
    | H : Znth i (app l2 (cons 0 nil)) 0 = 40 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (replace (Zlength l1 + (i + 1)) with (Zlength l1 + i + 1) by lia;
            rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat); lia).
  replace (Zlength l1 + (i + 1)) with (Zlength l1 + i + 1) by lia.
  symmetry.
  eapply (paren_good_prefix_flag_step_neg (Zlength l1 + i) (l1 ++ l2)
    (paren_level_upto (Zlength l1 + i) (l1 ++ l2) + 1)).
  - lia.
  - rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat). lia.
  - lia.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_4_2 : p119_match_parens_entail_wit_4_2.
Proof.
  unfold p119_match_parens_entail_wit_4_2.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth (Zlength l1 + i) (l1 ++ l2) 0 = 41).
  {
    rewrite Znth_app_right_119 by lia.
    replace (Zlength l1 + i - Zlength l1) with i by lia.
    match goal with
    | H : Znth i (app l2 (cons 0 nil)) 0 = 41 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (replace (Zlength l1 + (i + 1)) with (Zlength l1 + i + 1) by lia;
            rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat); lia).
  replace (Zlength l1 + (i + 1)) with (Zlength l1 + i + 1) by lia.
  symmetry.
  eapply (paren_good_prefix_flag_step_neg (Zlength l1 + i) (l1 ++ l2)
    (paren_level_upto (Zlength l1 + i) (l1 ++ l2) - 1)).
  - lia.
  - rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat). lia.
  - lia.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_4_3 : p119_match_parens_entail_wit_4_3.
Proof.
  unfold p119_match_parens_entail_wit_4_3.
  intros; pre_process; subst.
  pose proof (problem_119_pre_l2_char l1 l2 i ltac:(eassumption) ltac:(eassumption) ltac:(lia)) as [Hc | Hc].
  - assert (Znth i (l2 ++ cons 0 nil) 0 = 40) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
  - assert (Znth i (l2 ++ cons 0 nil) 0 = 41) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_4_4 : p119_match_parens_entail_wit_4_4.
Proof.
  unfold p119_match_parens_entail_wit_4_4.
  intros; pre_process; subst.
  pose proof (problem_119_pre_l2_char l1 l2 i ltac:(eassumption) ltac:(eassumption) ltac:(lia)) as [Hc | Hc].
  - assert (Znth i (l2 ++ cons 0 nil) 0 = 40) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
  - assert (Znth i (l2 ++ cons 0 nil) 0 = 41) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_4_5 : p119_match_parens_entail_wit_4_5.
Proof.
  unfold p119_match_parens_entail_wit_4_5.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth (Zlength l1 + i) (l1 ++ l2) 0 = 41).
  {
    rewrite Znth_app_right_119 by lia.
    replace (Zlength l1 + i - Zlength l1) with i by lia.
    match goal with
    | H : Znth i (app l2 (cons 0 nil)) 0 = 41 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (replace (Zlength l1 + (i + 1)) with (Zlength l1 + i + 1) by lia;
            rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat); lia).
  replace (Zlength l1 + (i + 1)) with (Zlength l1 + i + 1) by lia.
  destruct (paren_good_prefix_flag_bool (Zlength l1 + i) (l1 ++ l2)) as [Hflag | Hflag].
  - rewrite Hflag. symmetry. apply paren_good_prefix_flag_step_bad; lia.
  - rewrite Hflag. symmetry.
    eapply (paren_good_prefix_flag_step_nonneg (Zlength l1 + i) (l1 ++ l2)
      (paren_level_upto (Zlength l1 + i) (l1 ++ l2) - 1)).
    + lia.
    + exact Hflag.
    + rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat). lia.
    + lia.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_4_6 : p119_match_parens_entail_wit_4_6.
Proof.
  unfold p119_match_parens_entail_wit_4_6.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth (Zlength l1 + i) (l1 ++ l2) 0 = 40).
  {
    rewrite Znth_app_right_119 by lia.
    replace (Zlength l1 + i - Zlength l1) with i by lia.
    match goal with
    | H : Znth i (app l2 (cons 0 nil)) 0 = 40 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (replace (Zlength l1 + (i + 1)) with (Zlength l1 + i + 1) by lia;
            rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat); lia).
  replace (Zlength l1 + (i + 1)) with (Zlength l1 + i + 1) by lia.
  destruct (paren_good_prefix_flag_bool (Zlength l1 + i) (l1 ++ l2)) as [Hflag | Hflag].
  - rewrite Hflag. symmetry. apply paren_good_prefix_flag_step_bad; lia.
  - rewrite Hflag. symmetry.
    eapply (paren_good_prefix_flag_step_nonneg (Zlength l1 + i) (l1 ++ l2)
      (paren_level_upto (Zlength l1 + i) (l1 ++ l2) + 1)).
    + lia.
    + exact Hflag.
    + rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat). lia.
    + lia.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_5 : p119_match_parens_entail_wit_5.
Proof.
  unfold p119_match_parens_entail_wit_5.
  intros.
  pre_process; subst.
  entailer!.
  all: try solve [lia].
  all: try solve [replace (Zlength l1 + Zlength l2) with (Zlength l1 + i) by lia; congruence].
  all: try solve [
    replace (Zlength l1 + Zlength l2) with (Zlength l1 + i) by lia;
    pose proof (paren_good_prefix_flag_bool (Zlength l1 + i) (l1 ++ l2));
    lia
  ].
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_6 : p119_match_parens_entail_wit_6.
Proof.
  unfold p119_match_parens_entail_wit_6.
  intros.
  pre_process; subst.
Qed.

Lemma proof_of_p119_match_parens_entail_wit_7_1 : p119_match_parens_entail_wit_7_1.
Proof.
  unfold p119_match_parens_entail_wit_7_1.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth i (l2 ++ l1) 0 = 40).
  {
    rewrite Znth_app_left_119 by lia.
    match goal with
    | H : Znth i (app l2 (cons 0 nil)) 0 = 40 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat); lia).
  symmetry.
  eapply (paren_good_prefix_flag_step_neg i (l2 ++ l1)
    (paren_level_upto i (l2 ++ l1) + 1)).
  - lia.
  - rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat). lia.
  - lia.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_7_2 : p119_match_parens_entail_wit_7_2.
Proof.
  unfold p119_match_parens_entail_wit_7_2.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth i (l2 ++ l1) 0 = 41).
  {
    rewrite Znth_app_left_119 by lia.
    match goal with
    | H : Znth i (app l2 (cons 0 nil)) 0 = 41 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat); lia).
  symmetry.
  eapply (paren_good_prefix_flag_step_neg i (l2 ++ l1)
    (paren_level_upto i (l2 ++ l1) - 1)).
  - lia.
  - rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat). lia.
  - lia.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_7_3 : p119_match_parens_entail_wit_7_3.
Proof.
  unfold p119_match_parens_entail_wit_7_3.
  intros; pre_process; subst.
  pose proof (problem_119_pre_l2_char l1 l2 i ltac:(eassumption) ltac:(eassumption) ltac:(lia)) as [Hc | Hc].
  - assert (Znth i (l2 ++ cons 0 nil) 0 = 40) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
  - assert (Znth i (l2 ++ cons 0 nil) 0 = 41) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_7_4 : p119_match_parens_entail_wit_7_4.
Proof.
  unfold p119_match_parens_entail_wit_7_4.
  intros; pre_process; subst.
  pose proof (problem_119_pre_l2_char l1 l2 i ltac:(eassumption) ltac:(eassumption) ltac:(lia)) as [Hc | Hc].
  - assert (Znth i (l2 ++ cons 0 nil) 0 = 40) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
  - assert (Znth i (l2 ++ cons 0 nil) 0 = 41) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_7_5 : p119_match_parens_entail_wit_7_5.
Proof.
  unfold p119_match_parens_entail_wit_7_5.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth i (l2 ++ l1) 0 = 41).
  {
    rewrite Znth_app_left_119 by lia.
    match goal with
    | H : Znth i (app l2 (cons 0 nil)) 0 = 41 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat); lia).
  destruct (paren_good_prefix_flag_bool i (l2 ++ l1)) as [Hflag | Hflag].
  - rewrite Hflag. symmetry. apply paren_good_prefix_flag_step_bad; lia.
  - rewrite Hflag. symmetry.
    eapply (paren_good_prefix_flag_step_nonneg i (l2 ++ l1)
      (paren_level_upto i (l2 ++ l1) - 1)).
    + lia.
    + exact Hflag.
    + rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat). lia.
    + lia.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_7_6 : p119_match_parens_entail_wit_7_6.
Proof.
  unfold p119_match_parens_entail_wit_7_6.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth i (l2 ++ l1) 0 = 40).
  {
    rewrite Znth_app_left_119 by lia.
    match goal with
    | H : Znth i (app l2 (cons 0 nil)) 0 = 40 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat); lia).
  destruct (paren_good_prefix_flag_bool i (l2 ++ l1)) as [Hflag | Hflag].
  - rewrite Hflag. symmetry. apply paren_good_prefix_flag_step_bad; lia.
  - rewrite Hflag. symmetry.
    eapply (paren_good_prefix_flag_step_nonneg i (l2 ++ l1)
      (paren_level_upto i (l2 ++ l1) + 1)).
    + lia.
    + exact Hflag.
    + rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat). lia.
    + lia.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_8 : p119_match_parens_entail_wit_8.
Proof.
  unfold p119_match_parens_entail_wit_8.
  intros.
  pre_process; subst.
  assert (i = Zlength l2) by lia.
  subst i.
  replace (Zlength l2 + 0) with (Zlength l2) by lia.
  entailer!.
Qed.

Lemma proof_of_p119_match_parens_entail_wit_9_1 : p119_match_parens_entail_wit_9_1.
Proof.
  unfold p119_match_parens_entail_wit_9_1.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth (Zlength l2 + i) (l2 ++ l1) 0 = 40).
  {
    rewrite Znth_app_right_119 by lia.
    replace (Zlength l2 + i - Zlength l2) with i by lia.
    match goal with
    | H : Znth i (app l1 (cons 0 nil)) 0 = 40 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (replace (Zlength l2 + (i + 1)) with (Zlength l2 + i + 1) by lia;
            rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat); lia).
  replace (Zlength l2 + (i + 1)) with (Zlength l2 + i + 1) by lia.
  symmetry.
  eapply (paren_good_prefix_flag_step_neg (Zlength l2 + i) (l2 ++ l1)
    (paren_level_upto (Zlength l2 + i) (l2 ++ l1) + 1)).
  - lia.
  - rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat). lia.
  - lia.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_9_2 : p119_match_parens_entail_wit_9_2.
Proof.
  unfold p119_match_parens_entail_wit_9_2.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth (Zlength l2 + i) (l2 ++ l1) 0 = 41).
  {
    rewrite Znth_app_right_119 by lia.
    replace (Zlength l2 + i - Zlength l2) with i by lia.
    match goal with
    | H : Znth i (app l1 (cons 0 nil)) 0 = 41 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (replace (Zlength l2 + (i + 1)) with (Zlength l2 + i + 1) by lia;
            rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat); lia).
  replace (Zlength l2 + (i + 1)) with (Zlength l2 + i + 1) by lia.
  symmetry.
  eapply (paren_good_prefix_flag_step_neg (Zlength l2 + i) (l2 ++ l1)
    (paren_level_upto (Zlength l2 + i) (l2 ++ l1) - 1)).
  - lia.
  - rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat). lia.
  - lia.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_9_3 : p119_match_parens_entail_wit_9_3.
Proof.
  unfold p119_match_parens_entail_wit_9_3.
  intros; pre_process; subst.
  pose proof (problem_119_pre_l1_char l1 l2 i ltac:(eassumption) ltac:(eassumption) ltac:(lia)) as [Hc | Hc].
  - assert (Znth i (l1 ++ cons 0 nil) 0 = 40) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
  - assert (Znth i (l1 ++ cons 0 nil) 0 = 41) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_9_4 : p119_match_parens_entail_wit_9_4.
Proof.
  unfold p119_match_parens_entail_wit_9_4.
  intros; pre_process; subst.
  pose proof (problem_119_pre_l1_char l1 l2 i ltac:(eassumption) ltac:(eassumption) ltac:(lia)) as [Hc | Hc].
  - assert (Znth i (l1 ++ cons 0 nil) 0 = 40) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
  - assert (Znth i (l1 ++ cons 0 nil) 0 = 41) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_9_5 : p119_match_parens_entail_wit_9_5.
Proof.
  unfold p119_match_parens_entail_wit_9_5.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth (Zlength l2 + i) (l2 ++ l1) 0 = 41).
  {
    rewrite Znth_app_right_119 by lia.
    replace (Zlength l2 + i - Zlength l2) with i by lia.
    match goal with
    | H : Znth i (app l1 (cons 0 nil)) 0 = 41 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (replace (Zlength l2 + (i + 1)) with (Zlength l2 + i + 1) by lia;
            rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat); lia).
  replace (Zlength l2 + (i + 1)) with (Zlength l2 + i + 1) by lia.
  destruct (paren_good_prefix_flag_bool (Zlength l2 + i) (l2 ++ l1)) as [Hflag | Hflag].
  - rewrite Hflag. symmetry. apply paren_good_prefix_flag_step_bad; lia.
  - rewrite Hflag. symmetry.
    eapply (paren_good_prefix_flag_step_nonneg (Zlength l2 + i) (l2 ++ l1)
      (paren_level_upto (Zlength l2 + i) (l2 ++ l1) - 1)).
    + lia.
    + exact Hflag.
    + rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat). lia.
    + lia.
Qed. 

Lemma proof_of_p119_match_parens_entail_wit_9_6 : p119_match_parens_entail_wit_9_6.
Proof.
  unfold p119_match_parens_entail_wit_9_6.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth (Zlength l2 + i) (l2 ++ l1) 0 = 40).
  {
    rewrite Znth_app_right_119 by lia.
    replace (Zlength l2 + i - Zlength l2) with i by lia.
    match goal with
    | H : Znth i (app l1 (cons 0 nil)) 0 = 40 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (replace (Zlength l2 + (i + 1)) with (Zlength l2 + i + 1) by lia;
            rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat); lia).
  replace (Zlength l2 + (i + 1)) with (Zlength l2 + i + 1) by lia.
  destruct (paren_good_prefix_flag_bool (Zlength l2 + i) (l2 ++ l1)) as [Hflag | Hflag].
  - rewrite Hflag. symmetry. apply paren_good_prefix_flag_step_bad; lia.
  - rewrite Hflag. symmetry.
    eapply (paren_good_prefix_flag_step_nonneg (Zlength l2 + i) (l2 ++ l1)
      (paren_level_upto (Zlength l2 + i) (l2 ++ l1) + 1)).
    + lia.
    + exact Hflag.
    + rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat). lia.
    + lia.
Qed. 

Lemma proof_of_p119_match_parens_return_wit_1 : p119_match_parens_return_wit_1.
Proof.
  unfold p119_match_parens_return_wit_1.
  intros.
  pre_process; subst.
  entailer!.
  assert (Hflag21 : paren_good_prefix_flag (Zlength (l2 ++ l1)) (l2 ++ l1) = 0).
  {
    assert (Hneq : paren_good_prefix_flag (Zlength l2 + Zlength l1) (l2 ++ l1) <> 1).
    { replace (Zlength l2 + Zlength l1) with (Zlength l2 + i) by lia. congruence. }
    destruct (paren_good_prefix_flag_bool (Zlength l2 + Zlength l1) (l2 ++ l1)) as [Hflag0 | Hflag1].
    - replace (Zlength (l2 ++ l1)) with (Zlength l2 + Zlength l1) by (rewrite Zlength_app; lia).
      exact Hflag0.
    - exfalso. apply Hneq. exact Hflag1.
  }
  eapply problem_119_spec_false_from_flags; eauto.
  all: try (replace (Zlength (l1 ++ l2)) with (Zlength l1 + Zlength l2) by (rewrite Zlength_app; lia); eassumption).
  all: try exact Hflag21.
  all: try solve [solve_119_nonzero].
Qed. 

Lemma proof_of_p119_match_parens_return_wit_2 : p119_match_parens_return_wit_2.
Proof.
  unfold p119_match_parens_return_wit_2.
  intros.
  pre_process; subst.
  entailer!.
  eapply problem_119_spec_true_right; eauto.
  - rewrite <- (paren_total_app_comm l1 l2).
    replace (Zlength (l1 ++ l2)) with (Zlength l1 + Zlength l2) by (rewrite Zlength_app; lia).
    eassumption.
  - replace (Zlength (l2 ++ l1)) with (Zlength l2 + Zlength l1) by (rewrite Zlength_app; lia).
    replace (Zlength l2 + Zlength l1) with (Zlength l2 + i) by lia.
    congruence.
  - solve_119_nonzero.
  - solve_119_nonzero.
Qed. 

Lemma proof_of_p119_match_parens_return_wit_3 : p119_match_parens_return_wit_3.
Proof.
  unfold p119_match_parens_return_wit_3.
  intros.
  pre_process; subst.
  entailer!.
  eapply problem_119_spec_true_left; eauto.
  - replace (Zlength (l1 ++ l2)) with (Zlength l1 + Zlength l2) by (rewrite Zlength_app; lia).
    replace (Zlength l1 + Zlength l2) with (Zlength l1 + i) by lia.
    congruence.
  - replace (Zlength (l1 ++ l2)) with (Zlength l1 + Zlength l2) by (rewrite Zlength_app; lia).
    replace (Zlength l1 + Zlength l2) with (Zlength l1 + i) by lia.
    congruence.
  - solve_119_nonzero.
  - solve_119_nonzero.
Qed. 

Lemma proof_of_p119_match_parens_return_wit_4 : p119_match_parens_return_wit_4.
Proof.
  unfold p119_match_parens_return_wit_4.
  intros.
  pre_process; subst.
  entailer!.
  eapply problem_119_spec_false_from_level; eauto.
  - replace (Zlength (l1 ++ l2)) with (Zlength l1 + Zlength l2) by (rewrite Zlength_app; lia).
    replace (Zlength l1 + Zlength l2) with (Zlength l1 + i) by lia.
    congruence.
  - solve_119_nonzero.
  - solve_119_nonzero.
Qed. 

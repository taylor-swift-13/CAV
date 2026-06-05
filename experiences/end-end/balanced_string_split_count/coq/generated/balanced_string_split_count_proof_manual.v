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
From SimpleC.EE.CAV.verify_20260605_043229v_balanced_string_split_count Require Import balanced_string_split_count_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import balanced_string_split_count.
Local Open Scope sac.

Lemma lr_balance_app :
  forall l1 l2,
    lr_balance (l1 ++ l2) = lr_balance l1 + lr_balance l2.
Proof.
  induction l1.
  - simpl. intros. lia.
  - simpl. intros. rewrite IHl1. lia.
Qed.

Lemma nonzero_char_implies_lt_n :
  forall l n i,
    Zlength l = n ->
    0 <= i ->
    i <= n ->
    Znth i (app l (cons 0 nil)) 0 <> 0 ->
    i < n.
Proof.
  intros l n i Hlen Hlo Hle Hnz.
  destruct (Z_lt_ge_dec i n).
  - lia.
  - assert (i = n) by lia.
    subst i.
    rewrite app_Znth2 in Hnz by (rewrite Hlen; lia).
    rewrite Hlen in Hnz.
    replace (n - n) with 0 in Hnz by lia.
    simpl in Hnz.
    exfalso.
    apply Hnz.
    reflexivity.
Qed.

Lemma zero_char_implies_eq_n :
  forall l n i,
    Zlength l = n ->
    0 <= i ->
    i <= n ->
    (forall k : Z, (0 <= k < n)%Z -> Znth k l 0 <> 0) ->
    Znth i (app l (cons 0 nil)) 0 = 0 ->
    i = n.
Proof.
  intros l n i Hlen Hlo Hle Hall Hzero.
  destruct (Z_lt_ge_dec i n).
  - assert (Znth i l 0 <> 0) by (apply Hall; lia).
    rewrite app_Znth1 in Hzero by (rewrite Hlen; lia).
    contradiction.
  - lia.
Qed.

Lemma lr_balance_prefix_step :
  forall l i,
    0 <= i < Zlength l ->
    lr_balance (sublist 0 (i + 1) l) =
    lr_balance (sublist 0 i l) + lr_step (Znth i l 0).
Proof.
  intros l i Hi.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single 0) by lia.
  rewrite lr_balance_app.
  simpl.
  lia.
Qed.

Lemma go_sublist_step :
  forall l n i balance,
    Zlength l = n ->
    0 <= i < n ->
    balanced_string_split_count_go balance (sublist i n l) =
    (if Z.eq_dec (balance + lr_step (Znth i l 0)) 0 then 1 else 0) +
    balanced_string_split_count_go (balance + lr_step (Znth i l 0)) (sublist (i + 1) n l).
Proof.
  intros l n i balance Hlen Hi.
  rewrite <- Hlen.
  rewrite (sublist_split i (Zlength l) (i + 1) l) by lia.
  rewrite (sublist_single 0) by lia.
  simpl.
  reflexivity.
Qed.

Lemma proof_of_balanced_string_split_count_entail_wit_1 : balanced_string_split_count_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  unfold balanced_string_split_count_spec.
  rewrite sublist_self by lia.
  lia.
Qed.

Lemma proof_of_balanced_string_split_count_entail_wit_2_1 : balanced_string_split_count_entail_wit_2_1.
Proof.
  pre_process.
  assert (Hi_lt : i < n).
  { eapply nonzero_char_implies_lt_n; eauto; lia. }
  assert (Hnth : Znth i l 0 = 76).
  { pose proof H0 as Happ.
    rewrite app_Znth1 in Happ by (rewrite H14; lia).
    exact Happ. }
  entailer!.
  - rewrite <- H10.
    rewrite (go_sublist_step l n i balance H14) by lia.
    rewrite Hnth.
    unfold lr_step.
    destruct (Z.eq_dec 76 76); [|lia].
    rewrite H.
    destruct (Z.eq_dec 0 0).
    + replace
        (count + 1 + balanced_string_split_count_go 0 (sublist (i + 1) n l))
        with
        (count + (1 + balanced_string_split_count_go 0 (sublist (i + 1) n l)))
        by lia.
      reflexivity.
    + lia.
  - rewrite lr_balance_prefix_step by (rewrite H14; lia).
    rewrite H9.
    rewrite Hnth.
    unfold lr_step.
    destruct (Z.eq_dec 76 76); lia.
Qed.

Lemma proof_of_balanced_string_split_count_entail_wit_2_2 : balanced_string_split_count_entail_wit_2_2.
Proof.
  pre_process.
  assert (Hi_lt : i < n).
  { eapply nonzero_char_implies_lt_n; eauto; lia. }
  assert (Hnth_non76 : Znth i l 0 <> 76).
  { pose proof H0 as Happ.
    rewrite app_Znth1 in Happ by (rewrite H14; lia).
    exact Happ. }
  entailer!.
  - rewrite <- H10.
    rewrite (go_sublist_step l n i balance H14) by lia.
    unfold lr_step.
    destruct (Z.eq_dec (Znth i l 0) 76); [contradiction|].
    replace (balance + -1) with (balance - 1) by lia.
    rewrite H.
    destruct (Z.eq_dec 0 0).
    + replace
        (count + 1 + balanced_string_split_count_go 0 (sublist (i + 1) n l))
        with
        (count + (1 + balanced_string_split_count_go 0 (sublist (i + 1) n l)))
        by lia.
      reflexivity.
    + lia.
  - rewrite lr_balance_prefix_step by (rewrite H14; lia).
    rewrite H9.
    unfold lr_step.
    destruct (Z.eq_dec (Znth i l 0) 76); lia.
Qed.

Lemma proof_of_balanced_string_split_count_entail_wit_2_3 : balanced_string_split_count_entail_wit_2_3.
Proof.
  pre_process.
  assert (Hi_lt : i < n).
  { eapply nonzero_char_implies_lt_n; eauto; lia. }
  assert (Hnth_non76 : Znth i l 0 <> 76).
  { pose proof H0 as Happ.
    rewrite app_Znth1 in Happ by (rewrite H14; lia).
    exact Happ. }
  entailer!.
  - rewrite <- H10.
    rewrite (go_sublist_step l n i balance H14) by lia.
    unfold lr_step.
    destruct (Z.eq_dec (Znth i l 0) 76); [contradiction|].
    replace (balance + -1) with (balance - 1) by lia.
    destruct (Z.eq_dec (balance - 1) 0); [contradiction|reflexivity].
  - rewrite lr_balance_prefix_step by (rewrite H14; lia).
    rewrite H9.
    unfold lr_step.
    destruct (Z.eq_dec (Znth i l 0) 76); lia.
Qed.

Lemma proof_of_balanced_string_split_count_entail_wit_2_4 : balanced_string_split_count_entail_wit_2_4.
Proof.
  pre_process.
  assert (Hi_lt : i < n).
  { eapply nonzero_char_implies_lt_n; eauto; lia. }
  assert (Hnth : Znth i l 0 = 76).
  { pose proof H0 as Happ.
    rewrite app_Znth1 in Happ by (rewrite H14; lia).
    exact Happ. }
  entailer!.
  - rewrite <- H10.
    rewrite (go_sublist_step l n i balance H14) by lia.
    rewrite Hnth.
    unfold lr_step.
    destruct (Z.eq_dec 76 76); [|lia].
    destruct (Z.eq_dec (balance + 1) 0); [contradiction|reflexivity].
  - rewrite lr_balance_prefix_step by (rewrite H14; lia).
    rewrite H9.
    rewrite Hnth.
    unfold lr_step.
    destruct (Z.eq_dec 76 76); lia.
Qed.

Lemma proof_of_balanced_string_split_count_entail_wit_3 : balanced_string_split_count_entail_wit_3.
Proof.
  pre_process.
  assert (Hi_eq : i = n).
  { eapply zero_char_implies_eq_n; eauto; lia. }
  subst i.
  assert (Hbalance_done : balance = lr_balance l).
  { rewrite H7.
    rewrite sublist_self by (rewrite H12; lia).
    reflexivity. }
  assert (Hcount_done : count = balanced_string_split_count_spec l).
  { pose proof H8 as Hcount_eq.
    rewrite Zsublist_nil in Hcount_eq by lia.
    simpl in Hcount_eq.
    lia. }
  entailer!.
Qed.

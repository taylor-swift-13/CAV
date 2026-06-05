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
From SimpleC.EE.CAV.verify_20260605_054012v_count_asterisks_between_bars Require Import count_asterisks_between_bars_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import count_asterisks_between_bars.
Local Open Scope sac.

Lemma suffix_cons_from_Znth:
  forall (prefix suffix: list Z) (x: Z),
    Znth (Zlength prefix) (app (app prefix suffix) (cons 0 nil)) 0 = x ->
    x <> 0 ->
    exists suffix', suffix = cons x suffix'.
Proof.
  intros prefix suffix x Hnth Hx.
  destruct suffix as [| a suffix'].
  - rewrite app_nil_r in Hnth.
    rewrite app_Znth2 in Hnth.
    2: lia.
    replace (Zlength prefix - Zlength prefix) with 0 in Hnth by lia.
    rewrite Znth0_cons in Hnth.
    lia.
  - exists suffix'.
    rewrite <- app_assoc in Hnth.
    rewrite app_Znth2 in Hnth.
    2: lia.
    replace (Zlength prefix - Zlength prefix) with 0 in Hnth by lia.
    simpl in Hnth.
    rewrite Znth0_cons in Hnth.
    subst a.
    reflexivity.
Qed.

Lemma suffix_nil_from_lengths:
  forall (l prefix suffix: list Z) (n: Z),
    l = app prefix suffix ->
    Zlength prefix = n ->
    Zlength l = n ->
    suffix = nil.
Proof.
  intros l prefix suffix n Hl Hlen Hll.
  subst l.
  rewrite Zlength_app in Hll.
  assert (Zlength suffix = 0) by lia.
  apply Zlength_nil_inv.
  assumption.
Qed.

Lemma go_bar_from_inside_one:
  forall suffix,
    count_asterisks_between_bars_go 1 (cons 124 suffix) =
    count_asterisks_between_bars_go 0 suffix.
Proof.
  intros suffix.
  simpl.
  destruct (Z.eq_dec 124 124) as [_ | H].
  - reflexivity.
  - contradiction H; reflexivity.
Qed.

Lemma go_bar_from_inside_zero:
  forall suffix,
    count_asterisks_between_bars_go 0 (cons 124 suffix) =
    count_asterisks_between_bars_go 1 suffix.
Proof.
  intros suffix.
  simpl.
  destruct (Z.eq_dec 124 124) as [_ | H].
  - reflexivity.
  - contradiction H; reflexivity.
Qed.

Lemma go_star_from_inside_one:
  forall suffix,
    count_asterisks_between_bars_go 1 (cons 42 suffix) =
    1 + count_asterisks_between_bars_go 1 suffix.
Proof.
  intros suffix.
  simpl.
  destruct (Z.eq_dec 42 124) as [H | _].
  - lia.
  - destruct (Z.eq_dec 42 42) as [_ | H].
    + destruct (Z.eq_dec 1 1) as [_ | H1].
      * reflexivity.
      * contradiction H1; reflexivity.
    + contradiction H; reflexivity.
Qed.

Lemma go_star_from_inside_zero:
  forall suffix,
    count_asterisks_between_bars_go 0 (cons 42 suffix) =
    count_asterisks_between_bars_go 0 suffix.
Proof.
  intros suffix.
  simpl.
  destruct (Z.eq_dec 42 124) as [H | _].
  - lia.
  - destruct (Z.eq_dec 42 42) as [_ | H].
    + destruct (Z.eq_dec 0 1) as [H0 | _].
      * lia.
      * lia.
    + contradiction H; reflexivity.
Qed.

Lemma go_other_step:
  forall x inside suffix,
    x <> 124 ->
    x <> 42 ->
    count_asterisks_between_bars_go inside (cons x suffix) =
    count_asterisks_between_bars_go inside suffix.
Proof.
  intros x inside suffix H124 H42.
  simpl.
  destruct (Z.eq_dec x 124) as [Hx | Hx].
  - contradiction.
  - destruct (Z.eq_dec x 42) as [Hx42 | Hx42].
    + contradiction.
    + reflexivity.
Qed.

Lemma proof_of_count_asterisks_between_bars_entail_wit_1 : count_asterisks_between_bars_entail_wit_1.
Proof.
  pre_process.
  Exists nil l.
  entailer!.
Qed.

Lemma proof_of_count_asterisks_between_bars_entail_wit_2_1 : count_asterisks_between_bars_entail_wit_2_1.
Proof.
  pre_process.
  assert (inside = 1) by lia.
  subst inside.
  subst l.
  rewrite <- H3 in H0.
  rewrite <- H3 in H1.
  pose proof (suffix_cons_from_Znth prefix_2 suffix_2 124 H0 ltac:(lia)) as Hcons.
  destruct Hcons as [suffix' Hcons].
  subst suffix_2.
  Exists (app prefix_2 (cons 124 nil)) suffix'.
  entailer!.
  - pose proof (Zlength_nonneg suffix') as Hsuffix_len.
    rewrite Zlength_app in H13.
    rewrite Zlength_cons in H13.
    rewrite H3 in H13.
    lia.
  - rewrite Zlength_app_cons.
    rewrite H3.
    lia.
  - rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma proof_of_count_asterisks_between_bars_entail_wit_2_2 : count_asterisks_between_bars_entail_wit_2_2.
Proof.
  pre_process.
  subst inside.
  subst l.
  rewrite <- H3 in H0.
  rewrite <- H3 in H1.
  pose proof (suffix_cons_from_Znth prefix_2 suffix_2 124 H0 ltac:(lia)) as Hcons.
  destruct Hcons as [suffix' Hcons].
  subst suffix_2.
  Exists (app prefix_2 (cons 124 nil)) suffix'.
  entailer!.
  - pose proof (Zlength_nonneg suffix') as Hsuffix_len.
    rewrite Zlength_app in H13.
    rewrite Zlength_cons in H13.
    rewrite H3 in H13.
    lia.
  - rewrite Zlength_app_cons.
    rewrite H3.
    lia.
  - rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma proof_of_count_asterisks_between_bars_entail_wit_2_3 : count_asterisks_between_bars_entail_wit_2_3.
Proof.
  pre_process.
  assert (inside = 1) by lia.
  subst inside.
  subst l.
  rewrite <- H4 in H0.
  rewrite <- H4 in H2.
  pose proof (suffix_cons_from_Znth prefix_2 suffix_2 42 H0 ltac:(lia)) as Hcons.
  destruct Hcons as [suffix' Hcons].
  subst suffix_2.
  Exists (app prefix_2 (cons 42 nil)) suffix'.
  entailer!.
  - rewrite go_star_from_inside_one in H11.
    lia.
  - pose proof (Zlength_nonneg suffix') as Hsuffix_len.
    rewrite Zlength_app in H14.
    rewrite Zlength_cons in H14.
    rewrite H4 in H14.
    lia.
  - rewrite Zlength_app_cons.
    rewrite H4.
    lia.
  - rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma proof_of_count_asterisks_between_bars_entail_wit_2_4 : count_asterisks_between_bars_entail_wit_2_4.
Proof.
  pre_process.
  subst l.
  rewrite <- H3 in H.
  rewrite <- H3 in H0.
  rewrite <- H3 in H1.
  remember (Znth (Zlength prefix_2) ((prefix_2 ++ suffix_2) ++ 0 :: nil) 0) as x eqn:Hx.
  assert (Hx_ne_42 : x <> 42).
  { exact H. }
  assert (Hx_ne_124 : x <> 124).
  { exact H0. }
  assert (Hx_ne_0 : x <> 0).
  { exact H1. }
  pose proof
    (suffix_cons_from_Znth
       prefix_2 suffix_2 x (eq_sym Hx) Hx_ne_0) as Hcons.
  destruct Hcons as [suffix' Hcons].
  subst suffix_2.
  Exists (app prefix_2 (cons x nil)) suffix'.
  entailer!.
  - rewrite go_other_step in H10 by assumption.
    exact H10.
  - pose proof (Zlength_nonneg suffix') as Hsuffix_len.
    rewrite Zlength_app in H13.
    rewrite Zlength_cons in H13.
    rewrite H3 in H13.
    lia.
  - rewrite Zlength_app_cons.
    rewrite H3.
    lia.
  - rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma proof_of_count_asterisks_between_bars_entail_wit_2_5 : count_asterisks_between_bars_entail_wit_2_5.
Proof.
  pre_process.
  subst inside.
  subst l.
  rewrite <- H4 in H0.
  rewrite <- H4 in H2.
  pose proof (suffix_cons_from_Znth prefix_2 suffix_2 42 H0 ltac:(lia)) as Hcons.
  destruct Hcons as [suffix' Hcons].
  subst suffix_2.
  Exists (app prefix_2 (cons 42 nil)) suffix'.
  entailer!.
  - pose proof (Zlength_nonneg suffix') as Hsuffix_len.
    rewrite Zlength_app in H14.
    rewrite Zlength_cons in H14.
    rewrite H4 in H14.
    lia.
  - rewrite Zlength_app_cons.
    rewrite H4.
    lia.
  - rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma proof_of_count_asterisks_between_bars_entail_wit_3 : count_asterisks_between_bars_entail_wit_3.
Proof.
  pre_process.
  assert (i = n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - assert (Hnz : Znth i l 0 <> 0).
      {
        apply H12.
        lia.
      }
      rewrite app_Znth1 in H by lia.
      contradiction.
    - lia.
  }
  subst i.
  Exists prefix_2 suffix_2.
  entailer!.
  rewrite H13.
  cancel.
Qed.

Lemma proof_of_count_asterisks_between_bars_return_wit_1 : count_asterisks_between_bars_return_wit_1.
Proof.
  pre_process.
  assert (suffix = nil) as Hnil by (eapply suffix_nil_from_lengths; eauto).
  subst suffix.
  entailer!.
  simpl in *.
  unfold count_asterisks_between_bars_spec in *.
  lia.
Qed.

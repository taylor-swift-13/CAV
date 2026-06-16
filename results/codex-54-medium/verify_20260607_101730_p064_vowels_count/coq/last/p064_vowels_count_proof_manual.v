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
From SimpleC.EE.CAV.verify_20260607_101730_p064_vowels_count Require Import p064_vowels_count_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p064_vowels_count.
Local Open Scope sac.

Lemma count_regular_vowels_list_app_single :
  forall prefix x,
    count_regular_vowels_list (prefix ++ x :: nil) =
    count_regular_vowels_list prefix + (if is_regular_vowel x then 1 else 0).
Proof.
  induction prefix as [| a prefix IH]; intros x; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma count_regular_vowels_upto_full :
  forall l,
    count_regular_vowels_upto (Zlength l) l = count_regular_vowels_list l.
Proof.
  intros l.
  unfold count_regular_vowels_upto.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  rewrite firstn_all.
  reflexivity.
Qed.

Lemma Znth_app_zero_eq :
  forall l len i x,
    Zlength l = len ->
    0 <= i < len ->
    Znth i (app l (cons 0 nil)) 0 = x ->
    Znth i l 0 = x.
Proof.
  intros l len i x Hlen Hi H.
  rewrite app_Znth1 in H by (rewrite Hlen; lia).
  exact H.
Qed.

Lemma Znth_app_zero_neq :
  forall l len i x,
    Zlength l = len ->
    0 <= i < len ->
    Znth i (app l (cons 0 nil)) 0 <> x ->
    Znth i l 0 <> x.
Proof.
  intros l len i x Hlen Hi Hneq Heq.
  apply Hneq.
  rewrite app_Znth1 by (rewrite Hlen; lia).
  exact Heq.
Qed.

Lemma is_regular_vowel_false :
  forall x,
    x <> 97 ->
    x <> 101 ->
    x <> 105 ->
    x <> 111 ->
    x <> 117 ->
    x <> 65 ->
    x <> 69 ->
    x <> 73 ->
    x <> 79 ->
    x <> 85 ->
    is_regular_vowel x = false.
Proof.
  intros x H97 H101 H105 H111 H117 H65 H69 H73 H79 H85.
  unfold is_regular_vowel.
  destruct (Z.eqb_spec x 97); [contradiction|].
  destruct (Z.eqb_spec x 101); [contradiction|].
  destruct (Z.eqb_spec x 105); [contradiction|].
  destruct (Z.eqb_spec x 111); [contradiction|].
  destruct (Z.eqb_spec x 117); [contradiction|].
  destruct (Z.eqb_spec x 65); [contradiction|].
  destruct (Z.eqb_spec x 69); [contradiction|].
  destruct (Z.eqb_spec x 73); [contradiction|].
  destruct (Z.eqb_spec x 79); [contradiction|].
  destruct (Z.eqb_spec x 85); [contradiction|].
  reflexivity.
Qed.

Lemma count_regular_vowels_upto_step_nat :
  forall n l,
    (n < length l)%nat ->
    count_regular_vowels_list (firstn (S n) l) =
    count_regular_vowels_list (firstn n l) +
    (if is_regular_vowel (nth n l 0) then 1 else 0).
Proof.
  induction n as [| n IH]; intros l Hlt.
  - destruct l as [| x xs].
    + inversion Hlt.
    + simpl. lia.
  - destruct l as [| x xs].
    + inversion Hlt.
    + simpl in Hlt.
      simpl.
      change
        (count_regular_vowels_list
           match xs with
           | nil => nil
           | a :: l => a :: firstn n l
           end)
        with (count_regular_vowels_list (firstn (S n) xs)).
      rewrite IH by lia.
      lia.
Qed.

Lemma count_regular_vowels_upto_step :
  forall i l,
    0 <= i < Zlength l ->
    count_regular_vowels_upto (i + 1) l =
    count_regular_vowels_upto i l +
    (if is_regular_vowel (Znth i l 0) then 1 else 0).
Proof.
  intros i l [Hi0 Hilen].
  unfold count_regular_vowels_upto, Znth.
  rewrite Zlength_correct in Hilen.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  apply count_regular_vowels_upto_step_nat.
  lia.
Qed.

Ltac solve_common_pures :=
  repeat first
    [ dump_pre_spatial; auto
    | dump_pre_spatial; lia ].

Ltac rewrite_count_step :=
  match goal with
  | Hlen : Zlength ?l = ?len,
    Hi0 : 0 <= ?i,
    Hlt : ?i < ?len,
    Hcount : ?count = count_regular_vowels_upto ?i ?l |- _ =>
      rewrite Hcount;
      rewrite (count_regular_vowels_upto_step i l) by (rewrite Hlen; lia)
  end.

Ltac solve_vowel_step :=
  dump_pre_spatial;
  rewrite_count_step;
  match goal with
  | Hlen : Zlength ?l = ?len,
    Hi0 : 0 <= ?i,
    Hlt : ?i < ?len,
    Hchar : Znth ?i (?l ++ 0 :: nil) 0 = ?x |- _ =>
      assert (Znth i l 0 = x) as Hz by
        (rewrite app_Znth1 in Hchar by (rewrite Hlen; lia); exact Hchar);
      rewrite Hz;
      cbv [is_regular_vowel];
      entailer!
  end.

Ltac solve_nonvowel_step :=
  dump_pre_spatial;
  rewrite_count_step;
  match goal with
  | Hlen : Zlength ?l = ?len,
    Hi0 : 0 <= ?i,
    Hlt : ?i < ?len,
    H97 : Znth ?i (?l ++ 0 :: nil) 0 <> 97,
    H101 : Znth ?i (?l ++ 0 :: nil) 0 <> 101,
    H105 : Znth ?i (?l ++ 0 :: nil) 0 <> 105,
    H111 : Znth ?i (?l ++ 0 :: nil) 0 <> 111,
    H117 : Znth ?i (?l ++ 0 :: nil) 0 <> 117,
    H65 : Znth ?i (?l ++ 0 :: nil) 0 <> 65,
    H69 : Znth ?i (?l ++ 0 :: nil) 0 <> 69,
    H73 : Znth ?i (?l ++ 0 :: nil) 0 <> 73,
    H79 : Znth ?i (?l ++ 0 :: nil) 0 <> 79,
    H85 : Znth ?i (?l ++ 0 :: nil) 0 <> 85 |- _ =>
      assert (Znth i l 0 <> 97) as H97' by
        (intro Hz0; apply H97; now rewrite app_Znth1 by (rewrite Hlen; lia));
      assert (Znth i l 0 <> 101) as H101' by
        (intro Hz0; apply H101; now rewrite app_Znth1 by (rewrite Hlen; lia));
      assert (Znth i l 0 <> 105) as H105' by
        (intro Hz0; apply H105; now rewrite app_Znth1 by (rewrite Hlen; lia));
      assert (Znth i l 0 <> 111) as H111' by
        (intro Hz0; apply H111; now rewrite app_Znth1 by (rewrite Hlen; lia));
      assert (Znth i l 0 <> 117) as H117' by
        (intro Hz0; apply H117; now rewrite app_Znth1 by (rewrite Hlen; lia));
      assert (Znth i l 0 <> 65) as H65' by
        (intro Hz0; apply H65; now rewrite app_Znth1 by (rewrite Hlen; lia));
      assert (Znth i l 0 <> 69) as H69' by
        (intro Hz0; apply H69; now rewrite app_Znth1 by (rewrite Hlen; lia));
      assert (Znth i l 0 <> 73) as H73' by
        (intro Hz0; apply H73; now rewrite app_Znth1 by (rewrite Hlen; lia));
      assert (Znth i l 0 <> 79) as H79' by
        (intro Hz0; apply H79; now rewrite app_Znth1 by (rewrite Hlen; lia));
      assert (Znth i l 0 <> 85) as H85' by
        (intro Hz0; apply H85; now rewrite app_Znth1 by (rewrite Hlen; lia));
      rewrite (is_regular_vowel_false (Znth i l 0) H97' H101' H105' H111' H117' H65' H69' H73' H79' H85');
      entailer!
  end.

Lemma proof_of_p064_vowels_count_entail_wit_1 : p064_vowels_count_entail_wit_1.
Proof.
  pre_process.
  subst retval.
  split_pure_spatial.
  - cancel ((( &( "n" ) )) # Int |-> len).
    cancel (CharArray.full s_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact H3.
    + dump_pre_spatial. exact H5.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + unfold count_regular_vowels_upto.
      rewrite firstn_O.
      simpl.
      entailer!.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_1 : p064_vowels_count_entail_wit_2_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + solve_vowel_step.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_2 : p064_vowels_count_entail_wit_2_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + solve_vowel_step.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_3 : p064_vowels_count_entail_wit_2_3.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + solve_vowel_step.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_4 : p064_vowels_count_entail_wit_2_4.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + solve_vowel_step.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_5 : p064_vowels_count_entail_wit_2_5.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + solve_vowel_step.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_6 : p064_vowels_count_entail_wit_2_6.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + solve_vowel_step.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_7 : p064_vowels_count_entail_wit_2_7.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + solve_vowel_step.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_8 : p064_vowels_count_entail_wit_2_8.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + solve_vowel_step.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_9 : p064_vowels_count_entail_wit_2_9.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + solve_vowel_step.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_10 : p064_vowels_count_entail_wit_2_10.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + solve_vowel_step.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_11 : p064_vowels_count_entail_wit_2_11.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + solve_nonvowel_step.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_3 : p064_vowels_count_entail_wit_3.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      assert (Hi : i = len) by lia.
      subst i.
      exact H9.
Qed.

Lemma proof_of_p064_vowels_count_return_wit_1 : p064_vowels_count_return_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + solve_common_pures.
    + dump_pre_spatial.
      unfold problem_64_spec, last_y_add.
      match goal with
      | Hcount : count = count_regular_vowels_upto len l |- _ =>
          replace count with (count_regular_vowels_upto len l) by (symmetry; exact Hcount)
      end.
      rewrite <- H4.
      rewrite count_regular_vowels_upto_full.
      assert (HZlen_neq : Z.eqb (Zlength l) 0 = false).
      { rewrite H4. apply Z.eqb_neq. lia. }
      rewrite HZlen_neq.
      assert (Hz : Znth (Zlength l - 1) l 0 = 121).
      { rewrite H4. eapply Znth_app_zero_eq; eauto; lia. }
      unfold is_y.
      rewrite Hz.
      vm_compute.
      reflexivity.
Qed.

Lemma proof_of_p064_vowels_count_return_wit_2 : p064_vowels_count_return_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + solve_common_pures.
    + dump_pre_spatial.
      unfold problem_64_spec, last_y_add.
      match goal with
      | Hcount : count = count_regular_vowels_upto len l |- _ =>
          replace count with (count_regular_vowels_upto len l) by (symmetry; exact Hcount)
      end.
      rewrite <- H5.
      rewrite count_regular_vowels_upto_full.
      assert (HZlen_neq : Z.eqb (Zlength l) 0 = false).
      { rewrite H5. apply Z.eqb_neq. lia. }
      rewrite HZlen_neq.
      assert (Hz : Znth (Zlength l - 1) l 0 = 89).
      { rewrite H5. eapply Znth_app_zero_eq; eauto; lia. }
      unfold is_y.
      rewrite Hz.
      vm_compute.
      reflexivity.
Qed.

Lemma proof_of_p064_vowels_count_return_wit_3 : p064_vowels_count_return_wit_3.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial. auto.
    + dump_pre_spatial.
      unfold problem_64_spec, last_y_add.
      assert (Hlen0 : len = 0) by lia.
      rewrite Hlen0 in *.
      apply Zlength_nil_inv in H3.
      subst l.
      match goal with
      | Hcount : count = count_regular_vowels_upto 0 nil |- _ =>
          simpl in Hcount;
          rewrite Hcount
      end.
      reflexivity.
Qed.

Lemma proof_of_p064_vowels_count_return_wit_4 : p064_vowels_count_return_wit_4.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full s_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + solve_common_pures.
    + dump_pre_spatial.
      unfold problem_64_spec, last_y_add.
      match goal with
      | Hcount : count = count_regular_vowels_upto len l |- _ =>
          replace count with (count_regular_vowels_upto len l) by (symmetry; exact Hcount)
      end.
      rewrite <- H5.
      rewrite count_regular_vowels_upto_full.
      assert (HZlen_neq : Z.eqb (Zlength l) 0 = false).
      { rewrite H5. apply Z.eqb_neq. lia. }
      rewrite HZlen_neq.
      assert (Hnot89 : Znth (Zlength l - 1) l 0 <> 89).
      { rewrite H5. eapply Znth_app_zero_neq; eauto; lia. }
      assert (Hnot121 : Znth (Zlength l - 1) l 0 <> 121).
      { rewrite H5. eapply Znth_app_zero_neq; eauto; lia. }
      unfold is_y.
      assert (Hb121 : Z.eqb (Znth (Zlength l - 1) l 0) 121 = false).
      { apply Z.eqb_neq. exact Hnot121. }
      assert (Hb89 : Z.eqb (Znth (Zlength l - 1) l 0) 89 = false).
      { apply Z.eqb_neq. exact Hnot89. }
      rewrite Hb121.
      rewrite Hb89.
      simpl.
      rewrite Z.add_0_r.
      reflexivity.
Qed.

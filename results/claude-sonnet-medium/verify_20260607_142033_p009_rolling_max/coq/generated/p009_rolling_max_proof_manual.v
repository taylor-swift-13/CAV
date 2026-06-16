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
From SimpleC.EE.CAV.verify_20260607_142033_p009_rolling_max Require Import p009_rolling_max_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p009_rolling_max.
Local Open Scope sac.

(* Helper lemmas *)

Lemma running_max_val_ge_mx : forall mx l,
  mx <= running_max_val mx l.
Proof.
  intros mx l.
  generalize dependent mx.
  induction l; simpl; intros.
  - lia.
  - exact (Z.le_trans mx (Z.max mx a) (running_max_val (Z.max mx a) l)
             (Z.le_max_l mx a) (IHl (Z.max mx a))).
Qed.

Lemma running_max_val_app : forall mx l x,
  running_max_val mx (l ++ x :: nil) = Z.max (running_max_val mx l) x.
Proof.
  intros mx l x.
  generalize dependent mx.
  generalize dependent x.
  induction l; intros; simpl.
  - reflexivity.
  - rewrite IHl.
    reflexivity.
Qed.

Lemma running_max_val_sublist_app : forall mx lv i,
  0 <= i < Zlength lv ->
  running_max_val mx (sublist 0 (i + 1) lv) = Z.max (running_max_val mx (sublist 0 i lv)) (Znth i lv 0).
Proof.
  intros mx lv i Hi.
  assert (Hsub : sublist 0 (i + 1) lv = sublist 0 i lv ++ Znth i lv 0 :: nil).
  { rewrite (sublist_split 0 (i + 1) i lv) by lia.
    rewrite (sublist_single 0 i lv) by lia.
    reflexivity. }
  rewrite Hsub.
  rewrite running_max_val_app.
  reflexivity.
Qed.

Lemma rolling_max_f_Zlength : forall mx l,
  Zlength (rolling_max_f mx l) = Zlength l.
Proof.
  intros mx l.
  generalize dependent mx.
  induction l; intros; simpl rolling_max_f.
  - reflexivity.
  - rewrite Zlength_cons at 1.
    rewrite IHl.
    rewrite Zlength_cons.
    reflexivity.
Qed.

Lemma rolling_max_f_app_one : forall mx l x,
  rolling_max_f mx (l ++ x :: nil) = rolling_max_f mx l ++ running_max_val mx (l ++ x :: nil) :: nil.
Proof.
  intros mx l x.
  generalize dependent mx.
  generalize dependent x.
  induction l; intros; simpl.
  - reflexivity.
  - rewrite IHl.
    reflexivity.
Qed.

Lemma rolling_max_f_sublist_app : forall mx lv i,
  0 <= i < Zlength lv ->
  rolling_max_f mx (sublist 0 (i + 1) lv) = rolling_max_f mx (sublist 0 i lv) ++ running_max_val mx (sublist 0 (i + 1) lv) :: nil.
Proof.
  intros mx lv i Hi.
  assert (Hsub : sublist 0 (i + 1) lv = sublist 0 i lv ++ Znth i lv 0 :: nil).
  { rewrite (sublist_split 0 (i + 1) i lv) by lia.
    rewrite (sublist_single 0 i lv) by lia.
    reflexivity. }
  rewrite Hsub.
  rewrite rolling_max_f_app_one.
  reflexivity.
Qed.

Lemma rolling_max_f_Znth : forall mx l i,
  0 <= i < Zlength l ->
  Znth i (rolling_max_f mx l) 0 = running_max_val mx (sublist 0 (i + 1) l).
Proof.
  intros mx l.
  generalize dependent mx.
  induction l; intros.
  - rewrite Zlength_nil in H. lia.
  - destruct (Z.eq_dec i 0).
    + subst. simpl.
      reflexivity.
    + assert (0 <= i - 1 < Zlength l).
      { rewrite Zlength_cons in H. lia. }
      specialize (IHl (Z.max mx a) (i - 1) H0).
      simpl.
      rewrite Znth_cons by lia.
      replace (i - 0) with i by lia.
      rewrite sublist_cons1 by lia.
      replace (i + 1 - 1) with i by lia.
      replace (i - 1 + 1) with i in IHl by lia.
      simpl.
      exact IHl.
Qed.

Lemma running_max_val_ge_Znth : forall mx l i,
  0 <= i < Zlength l ->
  Znth i l 0 <= running_max_val mx l.
Proof.
  intros mx l.
  generalize dependent mx.
  induction l; intros.
  - rewrite Zlength_nil in H. lia.
  - destruct (Z.eq_dec i 0).
    + subst.
      rewrite Znth0_cons.
      simpl.
      assert (H0: Z.max mx a <= running_max_val (Z.max mx a) l).
      { apply running_max_val_ge_mx. }
      assert (H1: a <= Z.max mx a) by apply Z.le_max_r.
      assert (H2: a <= running_max_val (Z.max mx a) l).
      { exact (Z.le_trans _ _ _ H1 H0). }
      exact H2.
    + assert (0 <= i - 1 < Zlength l).
      { rewrite Zlength_cons in H. lia. }
      specialize (IHl (Z.max mx a) (i - 1) H0).
      rewrite Znth_cons by lia.
      replace (i - 0) with i by lia.
      simpl.
      exact IHl.
Qed.

Lemma running_max_val_eq_when_neq : forall mx a l,
  running_max_val (Z.max mx a) l <> a ->
  running_max_val mx l = running_max_val (Z.max mx a) l.
Proof.
  intros mx a l Hneq.
  generalize dependent mx.
  induction l as [|x l' IH]; intros.
  - simpl in Hneq.
    assert (Z.max mx a = mx).
    { destruct (Z.eq_dec (Z.max mx a) a).
      - contradiction.
      - apply Z.max_l. lia. }
    rewrite H. reflexivity.
  - simpl.
    assert (H : Z.max (Z.max mx x) a = Z.max (Z.max mx a) x) by lia.
    rewrite <- H.
    apply IH.
    rewrite H.
    exact Hneq.
Qed.

Lemma running_max_val_exists_Znth : forall mx l,
  (forall j, 0 <= j < Zlength l -> mx <= Znth j l 0) ->
  l <> nil ->
  exists j, 0 <= j < Zlength l /\ Znth j l 0 = running_max_val mx l.
Proof.
  intros mx l Hge Hnonempty.
  generalize dependent mx.
  induction l.
  - contradiction.
  - destruct l as [|b l'].
    + intros mx Hge.
      exists 0.
      split.
      * rewrite Zlength_cons, Zlength_nil. lia.
      * rewrite Znth0_cons. simpl.
        assert (mx <= a).
        { pose proof (Hge 0) as Hge0. rewrite Zlength_cons, Zlength_nil in Hge0. rewrite Znth0_cons in Hge0. apply Hge0. lia. }
        assert (Z.max mx a = a).
        { apply Z.max_r. lia. }
        rewrite H0. reflexivity.
    + intros mx Hge.
      assert (mx <= a).
      { pose proof (Hge 0) as Hge0. rewrite Zlength_cons in Hge0. rewrite Znth0_cons in Hge0. apply Hge0. pose proof (Zlength_nonneg (b :: l')). simpl. lia. }
      assert (H0 : forall j, 0 <= j < Zlength (b :: l') -> mx <= Znth j (b :: l') 0).
      { intros j Hj.
        assert (H0' : 0 <= j + 1 < Zlength (a :: b :: l')).
        { rewrite Zlength_cons. pose proof (Zlength_nonneg (b :: l')). lia. }
        specialize (Hge (j + 1)).
        specialize (Hge H0').
        rewrite Znth_cons in Hge by lia.
        assert (Hjj : j + 1 - 1 = j) by lia.
        rewrite Hjj in Hge.
        exact Hge. }
      assert (Hnil : b :: l' <> nil) by discriminate.
      specialize (IHl Hnil mx H0).
      destruct IHl as [j [Hj Hj_eq]].
      simpl.
      assert (Z.max mx a <= running_max_val (Z.max mx a) (b :: l')).
      { apply running_max_val_ge_mx. }
      destruct (Z.eq_dec (running_max_val (Z.max mx a) (b :: l')) a).
      * exists 0.
        split.
        -- rewrite Zlength_cons. lia.
        -- rewrite Znth0_cons. change (a = running_max_val (Z.max mx a) (b :: l')). rewrite e. reflexivity.
      * assert (Heq : running_max_val mx (b :: l') = running_max_val (Z.max mx a) (b :: l')).
        { apply running_max_val_eq_when_neq. exact n. }
        exists (j + 1).
        split.
        -- rewrite Zlength_cons. lia.
        -- rewrite Znth_cons by lia.
           replace (j + 1 - 1) with j by lia.
           rewrite Heq in Hj_eq.
           exact Hj_eq.
Qed.

Lemma problem_9_spec_rolling_max_f : forall lv,
  list_int_range lv ->
  problem_9_spec lv (rolling_max_f INT_MIN lv).
Proof.
  intros lv Hrange.
  unfold problem_9_spec.
  split.
  - rewrite rolling_max_f_Zlength. reflexivity.
  - intros i Hi.
    assert (0 <= i < Zlength lv).
    { rewrite rolling_max_f_Zlength in Hi. exact Hi. }
    rewrite rolling_max_f_Znth by exact H.
    split.
    + intros j Hj.
      assert (0 <= j < Zlength lv) by lia.
      assert (Znth j (sublist 0 (i + 1) lv) 0 <= running_max_val INT_MIN (sublist 0 (i + 1) lv)).
      { apply running_max_val_ge_Znth.
        rewrite Zlength_sublist; lia. }
      assert (Znth j (sublist 0 (i + 1) lv) 0 = Znth j lv 0).
      { apply Znth_sublist0; lia. }
      lia.
    + assert (forall j, 0 <= j < Zlength (sublist 0 (i + 1) lv) -> INT_MIN <= Znth j (sublist 0 (i + 1) lv) 0).
      {
        intros j Hj.
        assert (Hj' : 0 <= j < i + 1).
        { assert (Hlen : Zlength (sublist 0 (i + 1) lv) = i + 1) by (apply Zlength_sublist0; lia).
          rewrite Hlen in Hj. exact Hj. }
        assert (Hjj : Znth j (sublist 0 (i + 1) lv) 0 = Znth j lv 0).
        { apply Znth_sublist0. exact Hj'. }
        rewrite Hjj.
        unfold Znth.
        apply Hrange.
        assert (Hnat : (Z.to_nat j < length lv)%nat).
        { assert (Htmp : (Z.to_nat j < Z.to_nat (Zlength lv))%nat) by (apply Z2Nat.inj_lt; lia).
          rewrite Zlength_correct in Htmp.
          rewrite Nat2Z.id in Htmp.
          exact Htmp. }
        exact Hnat. }
      assert (sublist 0 (i + 1) lv <> nil).
      {
        intro Hnil.
        assert (Zlength (sublist 0 (i + 1) lv) = 0).
        { rewrite Hnil. reflexivity. }
        rewrite Zlength_sublist in H1; lia. }
      destruct (running_max_val_exists_Znth INT_MIN (sublist 0 (i + 1) lv) H0 H1) as [j [Hj Hj_eq]].
      exists j.
      split.
      * rewrite Zlength_sublist0 in Hj by lia. lia.
      * assert (Heq : Znth j lv 0 = Znth j (sublist 0 (i + 1) lv) 0).
        { symmetry. apply Znth_sublist0. rewrite Zlength_sublist0 in Hj by lia. exact Hj. }
        rewrite Heq.
        rewrite Hj_eq.
        reflexivity.
Qed.

(* Witness proofs *)

Lemma proof_of_p009_rolling_max_entail_wit_1 : p009_rolling_max_entail_wit_1.
Proof.
  pre_process.
  subst out_pre out_size_pre numbers_pre numbers_size_pre.
  Exists (@nil Z).
  sep_apply (IntArray.undef_full_to_undef_seg out0 out_size0).
  change (sublist 0 0 lv) with (@nil Z).
  rewrite (IntArray.seg_empty out0 0 0).
  rewrite H5.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption; try (simpl; reflexivity).
Qed.

Lemma proof_of_p009_rolling_max_entail_wit_2_1 : p009_rolling_max_entail_wit_2_1.
Proof.
  pre_process.
  prop_apply (IntArray.full_Zlength numbers0 numbers_size0 lv).
  Intros_p Hlen.
  Exists (app l_out_2 (cons max nil)).
  assert (Hbounds : 0 <= i < Zlength lv) by (split; [exact H1 |]; rewrite Hlen; exact H0).
  assert (Hrm : running_max_val INT_MIN (sublist 0 (i + 1) lv) = running_max_val INT_MIN (sublist 0 i lv)).
  {
    rewrite (running_max_val_sublist_app INT_MIN lv i Hbounds).
    assert (Hmax : Z.max (running_max_val INT_MIN (sublist 0 i lv)) (Znth i lv 0) = running_max_val INT_MIN (sublist 0 i lv)).
    { apply Z.max_l.
      rewrite H7 in H.
      exact H. }
    rewrite Hmax.
    reflexivity. }
  assert (Hrf : app l_out_2 (cons max nil) = rolling_max_f INT_MIN (sublist 0 (i + 1) lv)).
  {
    rewrite (rolling_max_f_sublist_app INT_MIN lv i Hbounds).
    rewrite Hrm.
    rewrite H8.
    rewrite H7.
    reflexivity. }
  rewrite Hrf.
  split_pure_spatial.
  - cancel (IntArray.full numbers0 numbers_size0 lv).
    cancel (IntArray.seg out0 0 (i + 1) (rolling_max_f INT_MIN (sublist 0 (i + 1) lv))).
    cancel (IntArray.undef_seg out0 (i + 1) numbers_size0).
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption; try (simpl; reflexivity).
Qed.

Lemma proof_of_p009_rolling_max_entail_wit_2_2 : p009_rolling_max_entail_wit_2_2.
Proof.
  pre_process.
  prop_apply (IntArray.full_Zlength numbers0 numbers_size0 lv).
  Intros_p Hlen.
  Exists (app l_out_2 (cons (Znth i lv 0) nil)).
  assert (Hbounds : 0 <= i < Zlength lv).
  { split. exact H1. rewrite Hlen. exact H0. }
  assert (Hrm : running_max_val INT_MIN (sublist 0 (i + 1) lv) = Znth i lv 0).
  {
    rewrite (running_max_val_sublist_app INT_MIN lv i Hbounds).
    assert (Hmax : Z.max (running_max_val INT_MIN (sublist 0 i lv)) (Znth i lv 0) = Znth i lv 0).
    { apply Z.max_r.
      rewrite <- H7.
      apply Z.lt_le_incl.
      apply Z.gt_lt.
      exact H. }
    rewrite Hmax.
    reflexivity. }
  assert (Hrf : app l_out_2 (cons (Znth i lv 0) nil) = rolling_max_f INT_MIN (sublist 0 (i + 1) lv)).
  {
    rewrite (rolling_max_f_sublist_app INT_MIN lv i Hbounds).
    rewrite Hrm.
    rewrite H8.
    reflexivity. }
  rewrite Hrf.
  split_pure_spatial.
  - cancel (IntArray.full numbers0 numbers_size0 lv).
    cancel (IntArray.seg out0 0 (i + 1) (rolling_max_f INT_MIN (sublist 0 (i + 1) lv))).
    cancel (IntArray.undef_seg out0 (i + 1) numbers_size0).
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption; try (simpl; reflexivity).
Qed.

Lemma proof_of_p009_rolling_max_return_wit_1 : p009_rolling_max_return_wit_1.
Proof.
  pre_process.
  Exists l_out.
  assert (Hi : i = numbers_size0) by lia.
  subst i.
  prop_apply IntArray.full_Zlength.
  Intros_p Hlen.
  assert (HlenZ : Zlength lv = numbers_size0) by (pose proof (Zlength_correct lv); lia).
  assert (Hsub : sublist 0 numbers_size0 lv = lv) by (apply sublist_self; exact (eq_sym HlenZ)).
  rewrite Hsub in *.
  rewrite IntArray.undef_seg_empty.
  sep_apply (IntArray.seg_to_full out0 0 numbers_size0 l_out).
  replace (out0 + 0 * sizeof ( INT )) with out0 by lia.
  replace (numbers_size0 - 0) with numbers_size0 by lia.
  split_pure_spatial.
  - cancel (IntArray.full numbers0 numbers_size0 lv).
    cancel (IntArray.full out0 numbers_size0 l_out).
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption; try (simpl; reflexivity); try (apply problem_9_spec_rolling_max_f; assumption).
Qed.

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
From SimpleC.EE.CAV.ground_truth_p015_string_sequence Require Import p015_string_sequence_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p015_string_sequence.
Require Import p015_string_sequence.
Require Import base_conversion_lib.
Require Import FunInd.
Local Open Scope sac.

Lemma p015_pow10_succ_nat : forall m : nat,
  10 ^ Z.of_nat (S m) = 10 * 10 ^ Z.of_nat m.
Proof.
  intro m.
  rewrite Nat2Z.inj_succ.
  rewrite Z.pow_succ_r by lia.
  reflexivity.
Qed.

Lemma p015_base_digits_10_len_pow : forall m n,
  0 < n ->
  n < 10 ^ Z.of_nat m ->
  Zlength (base_digits n 10) <= Z.of_nat m.
Proof.
  induction m as [|m IH]; intros n Hpos Hlt.
  - simpl in Hlt. lia.
  - rewrite base_digits_equation.
    replace (Z.leb 10 1) with false by reflexivity.
    replace (Z.leb n 0) with false by (symmetry; apply Z.leb_gt; lia).
    destruct (Z.ltb_spec n 10).
    + rewrite Zlength_cons. simpl. lia.
    + rewrite Zlength_app, Zlength_cons. simpl.
      assert (Hdivpos : 0 < n / 10) by (apply Z.div_str_pos; lia).
      assert (Hdivlt : n / 10 < 10 ^ Z.of_nat m).
      {
        apply Z.div_lt_upper_bound; [lia|].
        rewrite <- p015_pow10_succ_nat.
        exact Hlt.
      }
      specialize (IH (n / 10) Hdivpos Hdivlt).
      lia.
Qed.

Lemma p015_base_digits_pos_10_len_le_10 : forall n,
  0 <= n ->
  n < 10 ^ Z.of_nat 10 ->
  Zlength (base_digits_pos n 10) <= 10.
Proof.
  intros n Hnonneg Hlt.
  unfold base_digits_pos.
  destruct (Z.leb_spec n 0).
  - rewrite Zlength_nil. lia.
  - change 10 with (Z.of_nat 10%nat).
    apply p015_base_digits_10_len_pow; lia.
Qed.

Lemma p015_base_digits_pos_nonempty_10 : forall n,
  0 < n ->
  0 < Zlength (base_digits_pos n 10).
Proof.
  intros n Hn.
  unfold base_digits_pos.
  replace ((n <=? 0)%Z) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite base_digits_equation.
  replace (10 <=? 1)%Z with false by reflexivity.
  replace ((n <=? 0)%Z) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (n <? 10)%Z.
  - rewrite Zlength_cons, Zlength_nil. lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    pose proof (Zlength_nonneg (base_digits (n / 10) 10)).
    lia.
Qed.

Lemma p015_Zlength_repeat_Z : forall (x n : Z),
  0 <= n ->
  Zlength (repeat_Z x n) = n.
Proof.
  intros x n Hn.
  unfold repeat_Z.
  rewrite Zlength_correct, repeat_length.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma p015_Zlength_naive_repeat_Z : forall (x n : Z),
  0 <= n ->
  Zlength (naive_C_Rules.repeat_Z x n) = n.
Proof.
  intros x n Hn.
  unfold naive_C_Rules.repeat_Z.
  rewrite Zlength_correct, repeat_length.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma p015_replace_Znth_zero_cons : forall {A : Type} (x y : A) (l : list A),
  replace_Znth 0 x (y :: l) = x :: l.
Proof.
  intros.
  unfold replace_Znth, replace_nth.
  simpl.
  reflexivity.
Qed.

Lemma p015_base_digits_pos_step_10 : forall t,
  0 < t ->
  Zlength (base_digits_pos t 10) =
  Zlength (base_digits_pos (t / 10) 10) + 1.
Proof.
  intros t Ht.
  unfold base_digits_pos.
  replace ((t <=? 0)%Z) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite base_digits_equation.
  replace (10 <=? 1)%Z with false by reflexivity.
  replace ((t <=? 0)%Z) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (t <? 10)%Z eqn:Hlt.
  - apply Z.ltb_lt in Hlt.
    rewrite Zlength_cons.
    rewrite Z.div_small by lia.
    unfold base_digits_pos.
    replace (0 <=? 0)%Z with true by reflexivity.
    rewrite Zlength_nil.
    lia.
  - apply Z.ltb_ge in Hlt.
    rewrite Zlength_app, Zlength_cons.
    unfold base_digits_pos.
    replace ((t / 10 <=? 0)%Z) with false by
      (symmetry; apply Z.leb_gt; apply Z.div_str_pos; lia).
    rewrite Zlength_nil.
    lia.
Qed.

Lemma p015_base_digits_pos_step_list_10 : forall t,
  0 < t ->
  base_digits_pos t 10 =
  (base_digits_pos (t / 10) 10 ++ (48 + t mod 10) :: nil)%list.
Proof.
  intros t Ht.
  unfold base_digits_pos at 1.
  replace ((t <=? 0)%Z) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite base_digits_equation.
  replace (10 <=? 1)%Z with false by reflexivity.
  replace ((t <=? 0)%Z) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (t <? 10)%Z eqn:Hlt.
  - apply Z.ltb_lt in Hlt.
    rewrite Z.div_small by lia.
    rewrite Z.mod_small by lia.
    unfold base_digits_pos.
    replace (0 <=? 0)%Z with true by reflexivity.
    reflexivity.
  - apply Z.ltb_ge in Hlt.
    unfold base_digits_pos.
    replace ((t / 10 <=? 0)%Z) with false by
      (symmetry; apply Z.leb_gt; apply Z.div_str_pos; lia).
    reflexivity.
Qed.

Lemma proof_of_p015_string_sequence_safety_wit_19 : p015_string_sequence_safety_wit_19.
Proof.
  pre_process.
  assert (Hgeneral : forall n base,
    0 < n -> 1 < base ->
    Zlength (base_digits n base) = Zlength (base_digits_pos (n / base) base) + 1).
  {
    intros n base Hn Hb.
    functional induction (base_digits n base).
    - lia.
    - lia.
    - rewrite Zlength_cons.
      rewrite Z.div_small by lia.
      unfold base_digits_pos.
      simpl.
      lia.
    - simpl.
      unfold base_digits_pos.
      replace ((n / base <=? 0)%Z) with false by
        (symmetry; apply Z.leb_gt; apply Z.div_str_pos; lia).
      rewrite Zlength_app, Zlength_cons.
      simpl.
      lia.
  }
  assert (Hdigits_le : forall n base,
    0 < n -> 1 < base ->
    Zlength (base_digits n base) <= n).
  {
    intros n base Hn Hb.
    functional induction (base_digits n base).
    - lia.
    - lia.
    - rewrite Zlength_cons.
      simpl.
      lia.
    - rewrite Zlength_app, Zlength_cons.
      simpl.
      assert (0 < n / base) by (apply Z.div_str_pos; lia).
      assert (n / base < n) by (apply Z.div_lt; lia).
      lia.
  }
  assert (Hlen :
    Zlength (base_digits_pos t 10) =
    Zlength (base_digits_pos (t / 10) 10) + 1).
  {
    unfold base_digits_pos.
    replace ((t <=? 0)%Z) with false by (symmetry; apply Z.leb_gt; lia).
    apply Hgeneral; lia.
  }
  match goal with
  | Hstate : base_count_state i 10 t digits |- _ =>
      unfold base_count_state in Hstate;
      destruct Hstate as [_ [_ Hcount]]
  end.
  assert (0 <= Zlength (base_digits_pos (t / 10) 10)) by apply Zlength_nonneg.
  assert (Hstep : digits + 1 <= Zlength (base_digits_pos i 10)).
  {
    rewrite Hlen in Hcount.
    lia.
  }
  assert (Hi_len : Zlength (base_digits_pos i 10) <= i).
  {
    unfold base_digits_pos.
    replace ((i <=? 0)%Z) with false by (symmetry; apply Z.leb_gt; lia).
    apply Hdigits_le; lia.
  }
  assert (Hdigits_bound : digits + 1 <= i) by lia.
  assert (Hupper : digits + 1 <= INT_MAX) by lia.
  assert (Hlower : INT_MIN <= digits + 1) by lia.
  entailer!.
Qed.

Lemma proof_of_p015_string_sequence_safety_wit_34 : p015_string_sequence_safety_wit_34.
Proof.
  pre_process.
  assert (Hmod : 0 <= t % 10 < 10) by (apply Z.rem_bound_pos; lia).
  assert (Hupper : 48 + t % 10 <= INT_MAX) by lia.
  assert (Hlower : INT_MIN <= 48 + t % 10) by lia.
  entailer!.
  all: try exact Hlower; try exact Hupper.
Qed.

Lemma proof_of_p015_string_sequence_entail_wit_1 : p015_string_sequence_entail_wit_1.
Proof.
  pre_process.
  assert (Hseq1 : sequence_prefix 1 = 48 :: nil).
  {
    rewrite p015_sequence_prefix_1.
    reflexivity.
  }
  rewrite Hseq1.
  unfold CharArray.full, store_array.
  simpl store_array_rec.
  entailer!.
  - replace (0 + 1) with 1 by lia.
    replace (retval + 0 * sizeof(CHAR)) with (retval + 0) by lia.
    entailer!.
  - intros q [Hq0 Hq1].
    assert (q = 0) by lia.
    subst q.
    simpl.
    discriminate.
Qed.

Lemma proof_of_p015_string_sequence_entail_wit_2 : p015_string_sequence_entail_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full out k (sequence_prefix i)).
    cancel (CharArray.undef_seg out k cap).
  - split_pures; dump_pre_spatial; try lia; try assumption.
    unfold base_count_state.
    lia.
Qed.

Lemma proof_of_p015_string_sequence_entail_wit_3 : p015_string_sequence_entail_wit_3.
Proof.
  pre_process.
  assert (Hgeneral : forall n base,
    0 < n -> 1 < base ->
    Zlength (base_digits n base) = Zlength (base_digits_pos (n / base) base) + 1).
  {
    intros n base Hn Hb.
    functional induction (base_digits n base).
    - lia.
    - lia.
    - rewrite Zlength_cons.
      rewrite Z.div_small by lia.
      unfold base_digits_pos.
      simpl.
      lia.
    - simpl.
      unfold base_digits_pos.
      replace ((n / base <=? 0)%Z) with false by
        (symmetry; apply Z.leb_gt; apply Z.div_str_pos; lia).
      rewrite Zlength_app, Zlength_cons.
      simpl.
      lia.
  }
  assert (Hlen :
    Zlength (base_digits_pos t 10) =
    Zlength (base_digits_pos (t / 10) 10) + 1).
  {
    unfold base_digits_pos.
    replace ((t <=? 0)%Z) with false by (symmetry; apply Z.leb_gt; lia).
    apply Hgeneral; lia.
  }
  replace (t ÷ 10) with (t / 10)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  split_pure_spatial.
  - cancel (CharArray.full out k (sequence_prefix i)).
    cancel (CharArray.undef_seg out k cap).
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + apply Z.div_pos; lia.
    + match goal with
      | Hstate : base_count_state i 10 t digits |- _ =>
          destruct Hstate as [Ht_nonneg [Hdigits_nonneg Hcount]]
      end.
      unfold base_count_state.
      split.
      * apply Z.div_pos; lia.
      * split.
        -- lia.
        -- rewrite <- Hcount.
           rewrite Hlen.
           lia.
Qed.

Lemma proof_of_p015_string_sequence_entail_wit_4 : p015_string_sequence_entail_wit_4.
Proof.
  pre_process.
  assert (Hilen : Zlength (base_digits_pos i 10) <= 10).
  {
    apply p015_base_digits_pos_10_len_le_10; [lia|].
    change (10 ^ Z.of_nat 10) with 10000000000.
    lia.
  }
  assert (Ht0 : t = 0) by lia.
  assert (Hdigits_bound : digits <= 10).
  {
    match goal with
    | Hstate : base_count_state i 10 t digits |- _ =>
        rewrite Ht0 in Hstate;
        unfold base_count_state in Hstate;
        replace (Zlength (base_digits_pos 0 10)) with 0 in Hstate;
        [lia | unfold base_digits_pos; rewrite Zlength_nil; reflexivity]
    end.
  }
  unfold repeat_Z.
  simpl.
  replace (k + 1 + 0) with (k + 1) by lia.
  split_pure_spatial.
  - cancel (CharArray.full out (k + 1) (app (sequence_prefix i) (32 :: nil))).
    cancel (CharArray.undef_seg out (k + 1) cap).
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + change (k + 1 + digits + 12 * (n_pre - i) + 1 <= cap).
      assert (k + 1 + digits + 12 * (n_pre - i) + 1 <=
              k + 12 * (n_pre - i + 1) + 1) by lia.
      lia.
    + rewrite <- Ht0.
      assumption.
    + intros p [Hp0 Hp1].
      destruct (Z_lt_ge_dec p k) as [Hpk | Hpk].
      * rewrite app_Znth1 by lia.
        match goal with
        | Hnz : forall p : Z, 0 <= p < k -> _ |- _ => apply Hnz; lia
        end.
      * assert (p = k) by lia.
        subst p.
        rewrite app_Znth2 by lia.
        replace (k - Zlength (sequence_prefix i)) with 0 by lia.
        simpl.
        discriminate.
Qed.

Lemma proof_of_p015_string_sequence_entail_wit_5 : p015_string_sequence_entail_wit_5.
Proof.
  pre_process.
  rewrite repeat_Z_tail by lia.
  replace ((k + j) + 1) with (k + (j + 1)) by lia.
  replace (app (app (sequence_prefix i) (32 :: repeat_Z 0 j)) (0 :: nil))
    with (app (sequence_prefix i) (32 :: (repeat_Z 0 j ++ 0 :: nil)))
    by (rewrite <- app_assoc; reflexivity).
  split_pure_spatial.
  - cancel (CharArray.full out (k + (j + 1)) (app (sequence_prefix i) (32 :: (repeat_Z 0 j ++ 0 :: nil)))).
    cancel (CharArray.undef_seg out (k + (j + 1)) cap).
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_p015_string_sequence_entail_wit_6 : p015_string_sequence_entail_wit_6.
Proof.
  pre_process.
  assert (Hi_digits_nonempty : 0 < Zlength (base_digits i 10)).
  {
    rewrite base_digits_equation.
    replace (10 <=? 1)%Z with false by reflexivity.
    replace (i <=? 0)%Z with false by (symmetry; apply Z.leb_gt; lia).
    destruct (i <? 10)%Z eqn:Hilt.
    - rewrite Zlength_cons, Zlength_nil. lia.
    - rewrite Zlength_app, Zlength_cons, Zlength_nil.
      pose proof (Zlength_nonneg (base_digits (i / 10) 10)).
      lia.
  }
  assert (Hj : j = digits) by lia.
  subst j.
  Exists (repeat_Z 0 digits).
  split_pure_spatial.
  - cancel (CharArray.full out (k + digits) (app (sequence_prefix i) (32 :: repeat_Z 0 digits))).
    cancel (CharArray.undef_seg out (k + digits) cap).
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + intros _.
      unfold base_count_state in H15.
      unfold base_digits_pos in H15.
      replace ((i <=? 0)%Z) with false in H15 by
        (symmetry; apply Z.leb_gt; lia).
      replace ((0 <=? 0)%Z) with true in H15 by reflexivity.
      rewrite Zlength_nil in H15.
      lia.
    + unfold base_fill_full_state, base_fill_state.
      refine (ex_intro _ (@nil Z) _).
      split.
      * repeat split.
        -- lia.
        -- lia.
        -- unfold base_count_state in H15.
           unfold base_digits_pos in H15.
           replace ((i <=? 0)%Z) with false in H15 by
             (symmetry; apply Z.leb_gt; lia).
           replace ((0 <=? 0)%Z) with true in H15 by reflexivity.
           rewrite Zlength_nil in H15.
           unfold base_digits_pos.
           replace ((i <=? 0)%Z) with false by (symmetry; apply Z.leb_gt; lia).
           lia.
        -- unfold base_digits_pos.
           replace ((i <=? 0)%Z) with false by (symmetry; apply Z.leb_gt; lia).
           rewrite app_nil_r.
           reflexivity.
      * rewrite app_nil_r. reflexivity.
Qed.

Lemma proof_of_p015_string_sequence_entail_wit_7 : p015_string_sequence_entail_wit_7.
Proof.
  pre_process.
  Exists digits_l_2.
  replace (fill - 1 + 1) with fill by lia.
  split_pure_spatial.
  - cancel (CharArray.full out (k + digits) (app (sequence_prefix i) (32 :: digits_l_2))).
    cancel (CharArray.undef_seg out (k + digits) cap).
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_p015_string_sequence_entail_wit_8 : p015_string_sequence_entail_wit_8.
Proof.
  pre_process.
  pose proof (Z.rem_bound_pos t 10 ltac:(lia) ltac:(lia)) as Hrem.
  rewrite signed_last_nbits_eq by lia.
  replace (t % 10) with (t mod 10) by (symmetry; apply Z.rem_mod_nonneg; lia).
  replace (t ÷ 10) with (t / 10) by (symmetry; apply Z.quot_div_nonneg; lia).
  Exists (replace_Znth fill (48 + (t mod 10)) digits_l_2).
  split_pure_spatial.
  - rewrite replace_Znth_app_r by lia.
    rewrite replace_Znth_nothing by lia.
    replace (k + fill - Zlength (sequence_prefix i)) with (fill + 1) by lia.
    rewrite replace_Znth_cons by lia.
    replace (fill + 1 - 1) with fill by lia.
    cancel (CharArray.full out (k + digits)
      (app (sequence_prefix i) (32 :: replace_Znth fill (48 + (t mod 10)) digits_l_2))).
    cancel (CharArray.undef_seg out (k + digits) cap).
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + apply Z.div_pos; lia.
    + intros Hdivpos.
      match goal with
      | Hfull : base_fill_full_state _ _ _ _ _ |- _ =>
          unfold base_fill_full_state, base_fill_state in Hfull;
          destruct Hfull as [suffix0 [[Ht0 [Hfill0 [Hlen0 Hbase0]]] Hout0]]
      end.
      assert (Htpos : 0 < t).
      {
        destruct (Z_lt_ge_dec 0 t); [lia|].
        assert (t = 0) by lia.
        subst t.
        rewrite Z.div_0_l in Hdivpos by lia.
        lia.
      }
      rewrite (p015_base_digits_pos_step_10 t Htpos) in Hlen0.
      pose proof (p015_base_digits_pos_nonempty_10 (t / 10) ltac:(lia)).
      lia.
    + unfold base_fill_full_state, base_fill_state.
      match goal with
      | Hfull : base_fill_full_state _ _ _ _ _ |- _ =>
          unfold base_fill_full_state, base_fill_state in Hfull;
          destruct Hfull as [suffix [Hstate Hdigits]]
      end.
      refine (ex_intro _ (48 + (t mod 10) :: suffix) _).
      split.
      * destruct Hstate as [Ht0 [Hfill [Hlen Hbase]]].
        assert (Htpos : 0 < t).
        {
          destruct (Z_lt_ge_dec 0 t); [lia|].
          unfold base_digits_pos in Hlen.
          replace ((t <=? 0)%Z) with true in Hlen by
            (symmetry; apply Z.leb_le; lia).
          rewrite Zlength_nil in Hlen.
          lia.
        }
        repeat split.
        -- apply Z.div_pos; lia.
        -- lia.
        -- rewrite (p015_base_digits_pos_step_10 t) in Hlen by exact Htpos.
           lia.
        -- rewrite (p015_base_digits_pos_step_list_10 t) in Hbase by exact Htpos.
           rewrite <- app_assoc in Hbase.
           simpl in Hbase.
           exact Hbase.
      * subst digits_l_2.
        rewrite repeat_Z_tail by lia.
        rewrite <- app_assoc.
        rewrite replace_Znth_app_r by
          (rewrite p015_Zlength_repeat_Z by lia; lia).
        rewrite replace_Znth_nothing by
          (rewrite p015_Zlength_repeat_Z by lia; lia).
        replace (fill - Zlength (naive_C_Rules.repeat_Z 0 fill)) with 0 by
          (rewrite p015_Zlength_naive_repeat_Z by lia; lia).
        simpl.
        rewrite p015_replace_Znth_zero_cons.
        reflexivity.
Qed.

Lemma proof_of_p015_string_sequence_entail_wit_9 : p015_string_sequence_entail_wit_9.
Proof.
  pre_process.
  assert (Hi : i = n_pre + 1 \/ i <= n_pre) by lia.
  assert (Hfill0 : fill = 0).
  {
    unfold base_fill_full_state, base_fill_state in H17.
    destruct H17 as [suffix [Hstate Hdigits]].
    destruct Hstate as [Ht0 [Hfill [Hlen Hbase]]].
    unfold base_digits_pos in Hlen.
    replace ((t <=? 0)%Z) with true in Hlen by
      (symmetry; apply Z.leb_le; lia).
    rewrite Zlength_nil in Hlen.
    lia.
  }
  subst fill.
  assert (Hdigits_l : digits_l = base_digits i 10).
  {
    unfold base_fill_full_state, base_fill_state in H17.
    destruct H17 as [suffix [Hstate Hdigits]].
    destruct Hstate as [Ht0 [Hfill [Hlen Hbase]]].
    unfold base_digits_pos in Hbase.
    replace ((t <=? 0)%Z) with true in Hbase by
      (symmetry; apply Z.leb_le; lia).
    subst digits_l.
    simpl.
    symmetry.
    exact Hbase.
  }
  subst digits_l.
  rewrite p015_sequence_prefix_step by lia.
  split_pure_spatial.
  - cancel (CharArray.full out (k + digits) (app (sequence_prefix i) (32 :: base_digits i 10))).
    cancel (CharArray.undef_seg out (k + digits) cap).
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + unfold base_count_state in H16.
      unfold base_digits_pos in H16.
      replace ((i <=? 0)%Z) with false in H16 by
        (symmetry; apply Z.leb_gt; lia).
      replace ((0 <=? 0)%Z) with true in H16 by reflexivity.
      rewrite Zlength_nil in H16.
      try rewrite Zlength_app.
      try rewrite Zlength_cons.
      try rewrite Zlength_nil.
      lia.
    + intros p Hp.
      apply p015_sequence_prefix_step_Znth_nonzero.
      assert (Hdigits_len : digits = Zlength (base_digits i 10)).
      {
        pose proof H16 as Hcount.
        unfold base_count_state in Hcount.
        unfold base_digits_pos in Hcount.
        replace ((i <=? 0)%Z) with false in Hcount by
          (symmetry; apply Z.leb_gt; lia).
        replace ((0 <=? 0)%Z) with true in Hcount by reflexivity.
        rewrite Zlength_nil in Hcount.
        lia.
      }
      rewrite Zlength_app, Zlength_cons.
      lia.
Qed.

Lemma proof_of_p015_string_sequence_return_wit_1 : p015_string_sequence_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = n_pre + 1) by lia.
  subst i.
  Exists cap_2.
  Exists (sequence_prefix (n_pre + 1)).
  Exists k_2.
  split_pure_spatial.
  - cancel (CharArray.full out (k_2 + 1) (app (sequence_prefix (n_pre + 1)) (0 :: nil))).
    cancel (CharArray.undef_seg out (k_2 + 1) cap_2).
  - split_pures; dump_pre_spatial; try lia; try assumption.
    unfold problem_15_spec.
    reflexivity.
Qed.

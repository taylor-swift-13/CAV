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
From SimpleC.EE Require Import p044_change_base_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p044_change_base.
Require Import Recdef.
Local Open Scope sac.

(* ===== Helper Lemmas ===== *)

Lemma Zlength_repeat_Z : forall {A : Type} (a : A) n,
  0 <= n -> Zlength (repeat_Z a n) = n.
Proof.
  intros A a n Hn.
  unfold repeat_Z.
  rewrite Zlength_correct, repeat_length.
  lia.
Qed.

Lemma base_digits_length_pos : forall n base,
  0 < Zlength (base_digits n base).
Proof.
  intros n base.
  rewrite base_digits_equation.
  destruct (Z.leb base 1); [rewrite Zlength_cons, Zlength_nil; lia |].
  destruct (Z.leb n 0); [rewrite Zlength_cons, Zlength_nil; lia |].
  destruct (Z.ltb n base); [rewrite Zlength_cons, Zlength_nil; lia |].
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  pose proof (Zlength_nonneg (base_digits (n / base) base)). lia.
Qed.

Lemma base_digits_pos_length_pos : forall n base,
  0 < n -> 0 < Zlength (base_digits_pos n base).
Proof.
  intros n base Hn.
  unfold base_digits_pos.
  assert (Z.leb n 0 = false) by (apply Z.leb_nle; lia).
  rewrite H.
  apply base_digits_length_pos.
Qed.

Lemma base_digits_pos_div_step : forall t base,
  0 < t -> 2 <= base ->
  Zlength (base_digits_pos t base) = Zlength (base_digits_pos (t / base) base) + 1.
Proof.
  intros t base Ht Hbase.
  unfold base_digits_pos.
  assert (Htleb : Z.leb t 0 = false) by (apply Z.leb_nle; lia).
  rewrite Htleb.
  rewrite base_digits_equation.
  assert (Hbase1 : Z.leb base 1 = false) by (apply Z.leb_nle; lia).
  rewrite Hbase1, Htleb.
  destruct (Z.ltb t base) eqn:Htb.
  - apply Z.ltb_lt in Htb.
    assert (Hzero : t / base = 0) by (apply Z.div_small; lia).
    assert (Hleb : Z.leb (t / base) 0 = true) by (apply Z.leb_le; lia).
    rewrite Hleb.
    rewrite Zlength_cons, Zlength_nil. lia.
  - apply Z.ltb_ge in Htb.
    assert (Htb_pos : 0 < t / base) by (apply Z.div_str_pos; lia).
    assert (Htb_leb : Z.leb (t / base) 0 = false) by (apply Z.leb_nle; lia).
    rewrite Htb_leb.
    rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma base_digits_range_aux : forall (m : nat) (n base : Z),
  (Z.to_nat n <= m)%nat ->
  2 <= base -> 0 < n ->
  Forall (fun c => 48 <= c < 48 + base) (base_digits n base).
Proof.
  induction m as [|m IHm].
  - intros n base Hm Hbase Hn. lia.
  - intros n base Hm Hbase Hn.
    rewrite base_digits_equation.
    assert (Hb1 : Z.leb base 1 = false) by (apply Z.leb_nle; lia).
    assert (Hn0 : Z.leb n 0 = false) by (apply Z.leb_nle; lia).
    rewrite Hb1, Hn0.
    destruct (Z.ltb n base) eqn:Hnb.
    + apply Z.ltb_lt in Hnb.
      constructor; [lia | constructor].
    + apply Z.ltb_ge in Hnb.
      apply Forall_app.
      split.
      * apply IHm.
        { assert (Hlt : (Z.to_nat (n / base) < Z.to_nat n)%nat) by (
            apply Z2Nat.inj_lt; [apply Z.div_pos; lia | lia | apply Z.div_lt; lia]).
          lia. }
        { lia. }
        { apply Z.div_str_pos; lia. }
      * constructor; [| constructor].
        pose proof (Z.mod_pos_bound n base). lia.
Qed.

Lemma base_digits_range : forall n base,
  2 <= base -> 0 < n ->
  Forall (fun c => 48 <= c < 48 + base) (base_digits n base).
Proof.
  intros n base Hbase Hn.
  exact (base_digits_range_aux (Z.to_nat n) n base (Nat.le_refl _) Hbase Hn).
Qed.

Lemma base_digits_value_zero_aux : forall (m : nat) (n base : Z),
  (Z.to_nat n <= m)%nat ->
  2 <= base -> 0 < n ->
  fold_left (fun acc c => acc * base + (c - 48)) (base_digits n base) 0 = n.
Proof.
  induction m as [|m IHm].
  - intros n base Hm Hbase Hn. lia.
  - intros n base Hm Hbase Hn.
    rewrite base_digits_equation.
    assert (Hb1 : Z.leb base 1 = false) by (apply Z.leb_nle; lia).
    assert (Hn0 : Z.leb n 0 = false) by (apply Z.leb_nle; lia).
    rewrite Hb1, Hn0.
    destruct (Z.ltb n base) eqn:Hnb.
    + apply Z.ltb_lt in Hnb.
      cbn [fold_left]. ring.
    + apply Z.ltb_ge in Hnb.
      rewrite fold_left_app. cbn [fold_left].
      assert (Hdivval : fold_left (fun acc c : Z => acc * base + (c - 48))
                          (base_digits (n / base) base) 0 = n / base).
      { apply IHm.
        - assert (Hlt : (Z.to_nat (n / base) < Z.to_nat n)%nat) by (
            apply Z2Nat.inj_lt; [apply Z.div_pos; lia | lia | apply Z.div_lt; lia]).
          lia.
        - lia.
        - apply Z.div_str_pos; lia. }
      rewrite Hdivval.
      pose proof (Z.div_mod n base ltac:(lia)).
      rewrite Z.mul_comm. lia.
Qed.

Lemma base_digits_value_zero : forall n base,
  2 <= base -> 0 < n ->
  fold_left (fun acc c => acc * base + (c - 48)) (base_digits n base) 0 = n.
Proof.
  intros n base Hbase Hn.
  exact (base_digits_value_zero_aux (Z.to_nat n) n base (Nat.le_refl _) Hbase Hn).
Qed.

Lemma signed_last_nbits_char : forall r,
  0 <= r < 10 ->
  signed_last_nbits (48 + r) 8 = 48 + r.
Proof.
  intros r Hr.
  unfold signed_last_nbits.
  rewrite Z.mod_small by (split; [lia |]; vm_compute; lia).
  unfold zlt.
  destruct (Z_lt_dec (48 + r) (2 ^ (8 - 1))) as [Hlt | Hge].
  - reflexivity.
  - vm_compute in Hge. lia.
Qed.

Lemma replace_Znth_zero_singleton : forall {A : Type} (v a : A),
  replace_Znth 0 v (a :: nil) = v :: nil.
Proof.
  intros. unfold replace_Znth. simpl. reflexivity.
Qed.

(* ===== Main Proof Obligations ===== *)

Lemma proof_of_p044_change_base_safety_wit_25 : p044_change_base_safety_wit_25.
Proof.
  pre_process.
  assert (0 <= x mod base_pre < base_pre) by (apply Z.mod_pos_bound; lia).
  entailer!.
  lia.
Qed.

Lemma proof_of_p044_change_base_entail_wit_1 : p044_change_base_entail_wit_1.
Proof.
  pre_process.
  unfold base_count_state.
  entailer!.
  lia.
Qed.

Lemma proof_of_p044_change_base_entail_wit_2 : p044_change_base_entail_wit_2.
Proof.
  pre_process.
  unfold base_count_state in *.
  destruct H as [Ht [Hd Hcount]].
  rewrite Zquot_Zdiv_pos by lia.
  assert (Hdivpos : 0 <= t / base_pre) by (apply Z.div_pos; lia).
  assert (Hdivlt : t / base_pre < INT_MAX) by (
    apply Z.le_lt_trans with t; [apply Z.div_le_upper_bound; lia | lia]).
  assert (Hstep : Zlength (base_digits_pos t base_pre) =
                  Zlength (base_digits_pos (t / base_pre) base_pre) + 1) by
    (apply base_digits_pos_div_step; lia).
  entailer!.
  lia.
Qed.

Lemma proof_of_p044_change_base_entail_wit_3 : p044_change_base_entail_wit_3.
Proof.
  pre_process.
  unfold base_count_state in *.
  destruct H as [Ht [Hd Hcount]].
  assert (Ht0 : t = 0) by lia.
  subst t.
  assert (Hbdpos0 : Zlength (base_digits_pos 0 base_pre) = 0).
  { unfold base_digits_pos. simpl. rewrite Zlength_nil. reflexivity. }
  assert (Hdig : digits = Zlength (base_digits_pos x_pre base_pre)) by lia.
  assert (H1dig : 1 <= digits) by (
    rewrite Hdig; apply base_digits_pos_length_pos; lia).
  sep_apply CharArray.undef_full_to_undef_seg.
  rewrite (CharArray.full_empty retval 0).
  entailer!.
  - rewrite Hdig. reflexivity.
  - lia.
  - rewrite sepcon_comm.
    cancel (CharArray.undef_seg retval 0 (digits + 1)).
Qed.

Lemma proof_of_p044_change_base_entail_wit_4 : p044_change_base_entail_wit_4.
Proof.
  pre_process.
  rewrite <- (repeat_Z_tail 0 i) by lia.
  entailer!.
  rewrite <- app_assoc.
  cancel (CharArray.undef_seg out (i + 1) (total + 1)).
Qed.

Lemma proof_of_p044_change_base_entail_wit_5 : p044_change_base_entail_wit_5.
Proof.
  pre_process.
  assert (Hi : i = total + 1) by lia.
  subst i.
  rewrite (CharArray.undef_seg_empty out (total + 1)).
  rewrite sepcon_emp_equiv.
  rewrite (repeat_Z_tail 0 total) by lia.
  Left.
  Exists (repeat_Z 0 total).
  assert (Hxpre_pos : 0 < x_pre) by lia.
  assert (Hdig_pos : 0 < Zlength (base_digits_pos x_pre base_pre)) by
    (apply base_digits_pos_length_pos; lia).
  assert (Hdig_eq : digits = Zlength (base_digits_pos x_pre base_pre)) by lia.
  assert (H1dig : 1 <= digits) by (rewrite Hdig_eq; lia).
  entailer!.
  - unfold base_fill_full_state.
    exists [].
    split.
    + unfold base_fill_state.
      split; [lia |].
      split; [lia |].
      split; [| rewrite app_nil_r; unfold base_digits_pos;
                assert (Z.leb x_pre 0 = false) by (apply Z.leb_nle; lia);
                rewrite H0; reflexivity].
      rewrite app_nil_r.
      unfold base_digits_pos.
      assert (Z.leb x_pre 0 = false) by (apply Z.leb_nle; lia).
      rewrite H0. reflexivity.
    + rewrite app_nil_r. reflexivity.
  - lia.
  - cancel.
Qed.

Lemma proof_of_p044_change_base_entail_wit_6 : p044_change_base_entail_wit_6.
Proof.
  pre_process.
  unfold base_fill_full_state in H.
  destruct H as [suffix [Hfill Houtl]].
  unfold base_fill_state in Hfill.
  destruct Hfill as [Hx [Hdig [Hdiglen Hbase_eq]]].
  assert (Hmod : 0 <= x mod base_pre < base_pre) by (apply Z.mod_pos_bound; lia).
  assert (Hsnbits : signed_last_nbits (48 + x mod base_pre) 8 = 48 + x mod base_pre) by
    (apply signed_last_nbits_char; lia).
  rewrite Zquot_Zdiv_pos by lia.
  (* Common witness for both branches *)
  set (new_out_l := repeat_Z 0 (digits - 1) ++ [48 + x mod base_pre] ++ suffix).
  set (new_suffix := [48 + x mod base_pre] ++ suffix).
  (* The replace_Znth spatial rewrite *)
  assert (Hspatial :
    replace_Znth (digits - 1) (signed_last_nbits (48 + x mod base_pre) 8)
      (app out_l_2 (cons 0 nil)) =
    app new_out_l (cons 0 nil)).
  {
    rewrite Hsnbits.
    subst out_l_2 new_out_l.
    (* out_l_2 = repeat_Z 0 digits ++ suffix *)
    (* app out_l_2 [0] = (repeat_Z 0 digits ++ suffix) ++ [0] *)
    (* Step 1: replace_Znth (digits-1) v ((repeat_Z 0 digits ++ suffix) ++ [0])
               = replace_Znth (digits-1) v (repeat_Z 0 digits ++ suffix) ++ [0] *)
    rewrite replace_Znth_app_l.
    2: lia.
    2: { rewrite Zlength_app, Zlength_repeat_Z, (Zlength_nonneg suffix); lia. }
    (* Step 2: replace_Znth (digits-1) v (repeat_Z 0 digits ++ suffix)
               = replace_Znth (digits-1) v (repeat_Z 0 digits) ++ suffix *)
    rewrite replace_Znth_app_l.
    2: lia.
    2: { rewrite Zlength_repeat_Z; lia. }
    (* Step 3: rewrite repeat_Z 0 digits = repeat_Z 0 (digits-1) ++ [0] *)
    rewrite (repeat_Z_tail 0 (digits - 1)) by lia.
    replace (digits - 1 + 1) with digits by lia.
    (* Step 4: replace_Znth (digits-1) v (repeat_Z 0 (digits-1) ++ [0])
               = replace_Znth (digits-1) v (repeat_Z 0 (digits-1))
                 ++ replace_Znth 0 v [0] *)
    rewrite replace_Znth_app_r by (rewrite Zlength_repeat_Z; lia).
    (* Step 5: replace_Znth (digits-1) v (repeat_Z 0 (digits-1)) = repeat_Z 0 (digits-1) *)
    rewrite replace_Znth_nothing by (rewrite Zlength_repeat_Z; lia).
    rewrite Zlength_repeat_Z by lia.
    replace (digits - 1 - (digits - 1)) with 0 by lia.
    rewrite replace_Znth_zero_singleton.
    (* Result: repeat_Z 0 (digits-1) ++ [v] ++ suffix ++ [0] *)
    rewrite <- app_assoc.
    reflexivity.
  }
  (* Now case split on x / base_pre *)
  destruct (Z_le_gt_dec (x / base_pre) 0) as [Hle | Hgt].
  - (* Right branch: x / base_pre <= 0 *)
    Right.
    Exists new_out_l.
    assert (Hxdiv0 : x / base_pre = 0) by (
      apply Z.le_antisymm; [lia | apply Z.div_pos; lia]).
    assert (Hxlt : x < base_pre) by (
      destruct (Z.lt_ge_cases x base_pre); [lia |];
      assert (0 < x / base_pre) by (apply Z.div_str_pos; lia); lia).
    entailer!.
    + unfold base_fill_full_state.
      exists new_suffix.
      split.
      * unfold base_fill_state.
        split; [rewrite Hxdiv0; lia |].
        split; [lia |].
        split.
        ** rewrite Hxdiv0.
           unfold base_digits_pos at 1. simpl. rewrite Zlength_nil.
           rewrite Hdiglen.
           unfold base_digits_pos.
           assert (Z.leb x 0 = false) by (apply Z.leb_nle; lia).
           rewrite H0.
           rewrite base_digits_equation.
           assert (Z.leb base_pre 1 = false) by (apply Z.leb_nle; lia).
           rewrite H1, H0.
           assert (Z.ltb x base_pre = true) by (apply Z.ltb_lt; lia).
           rewrite H2.
           rewrite Zlength_cons, Zlength_nil. lia.
        ** rewrite Hxdiv0.
           unfold base_digits_pos at 1. simpl.
           rewrite <- Hbase_eq.
           unfold base_digits_pos.
           assert (Z.leb x 0 = false) by (apply Z.leb_nle; lia).
           rewrite H0.
           rewrite base_digits_equation.
           assert (Z.leb base_pre 1 = false) by (apply Z.leb_nle; lia).
           rewrite H1, H0.
           assert (Z.ltb x base_pre = true) by (apply Z.ltb_lt; lia).
           rewrite H2.
           unfold new_suffix.
           replace (48 + x mod base_pre) with (48 + x) by (
             rewrite Z.mod_small; lia).
           reflexivity.
      * unfold new_out_l, new_suffix.
        rewrite <- app_assoc. reflexivity.
    + rewrite Hxdiv0. lia.
    + rewrite <- Hspatial.
      cancel.
  - (* Left branch: x / base_pre > 0 *)
    Left.
    Exists new_out_l.
    assert (Hxge : x >= base_pre) by (
      destruct (Z.lt_ge_cases x base_pre); [|lia];
      assert (x / base_pre = 0) by (apply Z.div_small; lia); lia).
    entailer!.
    + unfold base_fill_full_state.
      exists new_suffix.
      split.
      * unfold base_fill_state.
        split; [apply Z.div_pos; lia |].
        split; [lia |].
        split.
        ** rewrite <- (base_digits_pos_div_step x base_pre) by lia. lia.
        ** (* base_digits x_pre base_pre = base_digits_pos (x/base_pre) base_pre ++ new_suffix *)
           rewrite <- Hbase_eq.
           unfold base_digits_pos.
           assert (Z.leb x 0 = false) by (apply Z.leb_nle; lia).
           rewrite H0.
           rewrite base_digits_equation.
           assert (Z.leb base_pre 1 = false) by (apply Z.leb_nle; lia).
           rewrite H1, H0.
           assert (Z.ltb x base_pre = false) by (apply Z.ltb_ge; lia).
           rewrite H2.
           assert (Htbpos : 0 < x / base_pre) by lia.
           assert (Z.leb (x / base_pre) 0 = false) by (apply Z.leb_nle; lia).
           rewrite H3.
           unfold new_suffix.
           rewrite <- app_assoc.
           reflexivity.
      * unfold new_out_l, new_suffix.
        rewrite <- app_assoc. reflexivity.
    + pose proof (base_digits_pos_length_pos (x / base_pre) base_pre ltac:(lia)).
      rewrite <- (base_digits_pos_div_step x base_pre) in H0 by lia.
      lia.
    + rewrite <- Hspatial.
      cancel.
Qed.

Lemma proof_of_p044_change_base_return_wit_1 : p044_change_base_return_wit_1.
Proof.
  pre_process.
  (* x <= 0 and 1 <= digits: contradiction via base_fill_full_state *)
  unfold base_fill_full_state in H.
  destruct H as [suffix [Hfill _]].
  unfold base_fill_state in Hfill.
  destruct Hfill as [Hx [Hdig [Hdiglen _]]].
  assert (Hx0 : x = 0) by lia.
  subst x.
  assert (Hbdp0 : Zlength (base_digits_pos 0 base_pre) = 0).
  { unfold base_digits_pos. simpl. rewrite Zlength_nil. reflexivity. }
  lia.
Qed.

Lemma proof_of_p044_change_base_return_wit_2 : p044_change_base_return_wit_2.
Proof.
  pre_process.
  assert (Hx0 : x = 0) by lia.
  subst x.
  unfold base_fill_full_state in H.
  destruct H as [suffix [Hfill Houtl]].
  unfold base_fill_state in Hfill.
  destruct Hfill as [_ [Hdig [Hdiglen Hbase_eq]]].
  assert (Hbdp0 : Zlength (base_digits_pos 0 base_pre) = 0).
  { unfold base_digits_pos. simpl. rewrite Zlength_nil. reflexivity. }
  assert (Hdig0 : digits = 0) by lia.
  subst digits.
  simpl in Houtl.
  rewrite app_nil_l in Hbase_eq.
  (* Hbase_eq: base_digits x_pre base_pre = suffix *)
  Exists (base_digits x_pre base_pre) total.
  entailer!.
  - intros k [Hk1 Hk2].
    pose proof (base_digits_range x_pre base_pre ltac:(lia) ltac:(lia)) as Hrange.
    rewrite Forall_forall in Hrange.
    assert (48 <= Znth k (base_digits x_pre base_pre) 0 < 48 + base_pre).
    { apply Hrange. apply Znth_In. lia. }
    lia.
  - lia.
  - unfold base_digits_pos in H2.
    assert (Z.leb x_pre 0 = false) by (apply Z.leb_nle; lia).
    rewrite H3 in H2. lia.
  - unfold problem_44_spec.
    split.
    + apply base_digits_range; lia.
    + apply base_digits_value_zero; lia.
  - rewrite <- Hbase_eq.
    rewrite Houtl.
    cancel.
Qed.

Lemma proof_of_p044_change_base_return_wit_3 : p044_change_base_return_wit_3.
Proof.
  pre_process.
  Exists (48 :: nil) 1.
  rewrite (CharArray.undef_seg_empty retval 2).
  entailer!.
  - intros k [Hk1 Hk2].
    assert (k = 0) by lia. subst k.
    simpl. lia.
  - rewrite Zlength_cons, Zlength_nil. lia.
  - unfold problem_44_spec.
    split.
    + constructor; [lia | constructor].
    + simpl. subst x_pre. lia.
  - simpl app.
    cancel.
Qed.

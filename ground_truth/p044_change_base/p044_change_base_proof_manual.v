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
From SimpleC.EE.CAV.ground_truth_p044_change_base Require Import p044_change_base_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.

Import naive_C_Rules.
Require Import p044_change_base.
Local Open Scope sac.
Require Import Coq.ZArith.Wf_Z.
Require Import Coq.micromega.Lia.
Require Import Recdef.
From compcert.lib Require Import Coqlib.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
Require Import string_bridge.

Local Open Scope list_scope.

(* Proof helpers moved from p044_change_base.v so public contract files expose definitions only. *)

Lemma Zlength_repeat_Z : forall {A : Type} (a : A) n,
  0 <= n -> Zlength (repeat_Z a n) = n.
Proof.
  intros A a n Hn.
  unfold repeat_Z.
  rewrite Zlength_correct, repeat_length.
  lia.
Qed.
Lemma repeat_Z_tail : forall {A : Type} (a : A) n,
  0 <= n -> repeat_Z a (n + 1) = repeat_Z a n ++ [a].
Proof.
  intros A a n Hn.
  unfold repeat_Z.
  replace (Z.to_nat (n + 1)) with (Z.to_nat n + 1)%nat by lia.
  rewrite repeat_app.
  reflexivity.
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
  pose proof (Zlength_nonneg (base_digits (n / base) base)).
  lia.
Qed.
Lemma base_digits_nonempty : forall n base,
  base_digits n base <> [].
Proof.
  intros n base Hnil.
  pose proof (base_digits_length_pos n base).
  rewrite Hnil, Zlength_nil in H.
  lia.
Qed.
Lemma base_digits_pos_length_pos : forall n base,
  0 < n -> 0 < Zlength (base_digits_pos n base).
Proof.
  intros n base Hn.
  unfold base_digits_pos.
  match goal with | |- context[?a <=? ?b] => replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia) end.
  apply base_digits_length_pos.
Qed.
Lemma base_digits_length_pos_le_aux : forall m n base,
  (Z.to_nat n <= m)%nat ->
  0 < n -> 2 <= base -> Zlength (base_digits n base) <= n.
Proof.
  induction m as [|m IHm].
  - intros n base Hm Hn Hbase.
    assert (Z.to_nat n = 0%nat) by lia.
    pose proof (Z2Nat.id n ltac:(lia)).
    rewrite H in H0. simpl in H0. lia.
  - intros n base Hm Hn Hbase.
    rewrite base_digits_equation.
    match goal with | |- context[?a <=? ?b] => replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia) end.
    match goal with | |- context[?a <=? ?b] => replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia) end.
    destruct (Z.ltb_spec n base).
    + rewrite Zlength_cons, Zlength_nil. lia.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil.
      assert (Hdivpos : 0 < n / base) by (apply Z.div_str_pos; lia).
      assert (Hlt_nat : (Z.to_nat (n / base) < Z.to_nat n)%nat) by
        (apply Z2Nat.inj_lt; [apply Z.div_pos; lia | lia | apply Z.div_lt; lia]).
      specialize (IHm (n / base) base ltac:(lia) Hdivpos Hbase).
      lia.
Qed.
Lemma base_digits_length_pos_le : forall n base,
  0 < n -> 2 <= base -> Zlength (base_digits n base) <= n.
Proof.
  intros n base Hn Hbase.
  apply (base_digits_length_pos_le_aux (Z.to_nat n)); lia.
Qed.
Lemma base_digits_pos_step : forall n base,
  0 < n ->
  2 <= base ->
  base_digits_pos n base =
    base_digits_pos (n / base) base ++ [48 + n mod base].
Proof.
  intros n base Hn Hbase.
  unfold base_digits_pos at 1.
  match goal with | |- context[?a <=? ?b] => replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia) end.
  rewrite base_digits_equation.
  match goal with | |- context[?a <=? ?b] => replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia) end.
  match goal with | |- context[?a <=? ?b] => replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia) end.
  destruct (Z.ltb_spec n base).
  - assert (Hdiv0 : n / base = 0) by (apply Z.div_small; lia).
    rewrite Hdiv0.
    unfold base_digits_pos.
    match goal with | |- context[?a <=? ?a] => replace (a <=? a) with true by (symmetry; apply Z.leb_le; lia) end.
    rewrite Z.mod_small by lia.
    reflexivity.
  - assert (Hdivpos : 0 < n / base) by (apply Z.div_str_pos; lia).
    unfold base_digits_pos at 1.
    match goal with | |- context[?a <=? ?b] => replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia) end.
    reflexivity.
Qed.
Lemma base_count_state_init : forall orig base,
  0 <= orig -> base_count_state orig base orig 0.
Proof.
  intros orig base Horig.
  unfold base_count_state.
  repeat split; lia.
Qed.
Lemma base_count_state_step : forall orig base t digits,
  0 < t ->
  2 <= base ->
  base_count_state orig base t digits ->
  base_count_state orig base (t / base) (digits + 1).
Proof.
  intros orig base t digits Ht Hbase Hstate.
  unfold base_count_state in *.
  destruct Hstate as [Ht_nonneg [Hdigits Hlen]].
  rewrite (base_digits_pos_step t base) in Hlen by lia.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen.
  repeat split; try lia.
  apply Z.div_pos; lia.
Qed.
Lemma base_count_state_done : forall orig base digits,
  0 < orig ->
  base_count_state orig base 0 digits ->
  digits = Zlength (base_digits orig base).
Proof.
  intros orig base digits Horig Hstate.
  unfold base_count_state in Hstate.
  destruct Hstate as [_ [_ Hlen]].
  unfold base_digits_pos in Hlen.
  replace (0 <=? 0) with true in Hlen by (symmetry; apply Z.leb_le; lia).
  rewrite Zlength_nil in Hlen.
  match type of Hlen with context[?a <=? ?b] => replace (a <=? b) with false in Hlen by (symmetry; apply Z.leb_gt; lia) end.
  lia.
Qed.
Lemma base_fill_full_state_init : forall orig base digits,
  0 < orig ->
  digits = Zlength (base_digits orig base) ->
  base_fill_full_state orig base orig digits (repeat_Z 0 digits).
Proof.
  intros orig base digits Horig Hdigits.
  unfold base_fill_full_state.
  exists [].
  split.
  - unfold base_fill_state.
    split; [lia |].
    split.
    + rewrite Hdigits.
      pose proof (base_digits_length_pos orig base).
      lia.
    + split.
      * unfold base_digits_pos.
        replace (orig <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
        exact Hdigits.
      * unfold base_digits_pos.
        replace (orig <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
        rewrite app_nil_r.
        reflexivity.
  - rewrite app_nil_r.
    reflexivity.
Qed.
Lemma base_fill_full_state_positive_digits : forall orig base x digits out_l,
  0 < x ->
  2 <= base ->
  base_fill_full_state orig base x digits out_l ->
  0 < digits.
Proof.
  intros orig base x digits out_l Hx Hbase Hfull.
  unfold base_fill_full_state, base_fill_state in Hfull.
  destruct Hfull as [suffix [[_ [_ [Hdigits _]]] _]].
  rewrite Hdigits.
  apply base_digits_pos_length_pos; lia.
Qed.
Lemma signed_last_nbits_char : forall r,
  0 <= r < 10 ->
  signed_last_nbits (48 + r) 8 = 48 + r.
Proof.
  intros r Hr.
  unfold signed_last_nbits.
  rewrite Z.mod_small by (split; [lia | change (2 ^ 8) with 256; lia]).
  unfold zlt.
  destruct (Z_lt_dec (48 + r) (2 ^ (8 - 1))) as [Hlt | Hge].
  - reflexivity.
  - exfalso. change (2 ^ (8 - 1)) with 128 in Hge. lia.
Qed.
Lemma replace_Znth_zero_singleton : forall {A : Type} (v a : A),
  replace_Znth 0 v [a] = [v].
Proof.
  intros. unfold replace_Znth. simpl. reflexivity.
Qed.
Lemma replace_Znth_repeat_Z_tail : forall digits suffix v,
  0 <= digits ->
  replace_Znth digits v (repeat_Z 0 (digits + 1) ++ suffix) =
    repeat_Z 0 digits ++ [v] ++ suffix.
Proof.
  intros digits suffix v Hdigits.
  unfold replace_Znth, repeat_Z.
  replace (Z.to_nat (digits + 1)) with (Z.to_nat digits + 1)%nat by lia.
  rewrite repeat_app. simpl.
  rewrite <- app_assoc.
  rewrite (replace_nth_app_r (Z.to_nat digits) v
             (repeat 0 (Z.to_nat digits)) ([0] ++ suffix))
    by (rewrite repeat_length; lia).
  assert (Hpast: forall n, replace_nth n (repeat 0 n) v = repeat 0 n).
  {
    induction n; simpl; congruence.
  }
  rewrite Hpast.
  rewrite repeat_length.
  replace (Z.to_nat digits - Z.to_nat digits)%nat with O by lia.
  simpl.
  reflexivity.
Qed.
Lemma base_fill_full_state_step : forall orig base x digits out_l,
  0 < x ->
  2 <= base ->
  base < 10 ->
  base_fill_full_state orig base x (digits + 1) out_l ->
  base_fill_full_state orig base (x / base) digits
    (replace_Znth digits (signed_last_nbits (48 + x mod base) 8) out_l).
Proof.
  intros orig base x digits out_l Hx Hbase Hbase_hi Hfull.
  unfold base_fill_full_state in Hfull.
  destruct Hfull as [suffix [Hfill Hout]].
  unfold base_fill_state in Hfill.
  destruct Hfill as [Hx_nonneg [Hdigits_nonneg [Hdigits_len Hbase_eq]]].
  assert (Hstep := base_digits_pos_step x base Hx Hbase).
  assert (Hmod : 0 <= x mod base < base) by (apply Z.mod_pos_bound; lia).
  assert (Hsigned : signed_last_nbits (48 + x mod base) 8 = 48 + x mod base)
    by (apply signed_last_nbits_char; lia).
  unfold base_fill_full_state.
  exists ([48 + x mod base] ++ suffix).
  split.
  - unfold base_fill_state.
    repeat split.
    + apply Z.div_pos; lia.
    + pose proof (Zlength_nonneg (base_digits_pos (x / base) base)).
      rewrite Hstep in Hdigits_len.
      rewrite Zlength_app, Zlength_cons, Zlength_nil in Hdigits_len.
      lia.
    + rewrite Hstep in Hdigits_len.
      rewrite Zlength_app, Zlength_cons, Zlength_nil in Hdigits_len.
      lia.
    + rewrite Hbase_eq.
      rewrite Hstep.
      rewrite app_assoc.
      reflexivity.
  - subst out_l.
    rewrite Hsigned.
    apply replace_Znth_repeat_Z_tail.
    pose proof (Zlength_nonneg (base_digits_pos (x / base) base)).
    rewrite Hstep in Hdigits_len.
    rewrite Zlength_app, Zlength_cons, Zlength_nil in Hdigits_len.
    lia.
Qed.
Lemma Zlength_replace_Znth_44 : forall {A : Type} (l : list A) n (v : A),
  Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros.
  apply Zlength_replace_Znth.
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
    match goal with | |- context[?a <=? ?b] => replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia) end.
    match goal with | |- context[?a <=? ?b] => replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia) end.
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
Lemma p044_Forall_Znth_nonzero : forall l p,
  Forall (fun x => x <> 0) l ->
  0 <= p < Zlength l ->
  Znth p l 0 <> 0.
Proof.
  intros l p Hforall Hp.
  unfold Znth.
  apply Forall_forall with (x := nth (Z.to_nat p) l 0) in Hforall.
  - exact Hforall.
  - apply nth_In.
    rewrite Zlength_correct in Hp.
    lia.
Qed.
Lemma base_digits_nonzero_forall : forall n base,
  2 <= base -> 0 < n ->
  Forall (fun c => c <> 0) (base_digits n base).
Proof.
  intros n base Hbase Hn.
  pose proof (base_digits_range n base Hbase Hn) as Hrange.
  induction Hrange.
  - constructor.
  - constructor; lia || assumption.
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
    match goal with | |- context[?a <=? ?b] => replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia) end.
    match goal with | |- context[?a <=? ?b] => replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia) end.
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
Lemma problem_44_spec_intro : forall x base output,
  0 < x ->
  2 <= base ->
  output = base_digits x base ->
  problem_44_spec x base output.
Proof.
  intros x base output Hx Hbase Hout.
  subst output.
  unfold problem_44_spec.
  split.
  - apply base_digits_range; lia.
  - apply base_digits_value_zero; lia.
Qed.
Lemma problem_44_spec_zero : forall base,
  2 <= base ->
  problem_44_spec 0 base [48].
Proof.
  intros base Hbase.
  unfold problem_44_spec.
  split.
  - constructor; [lia | constructor].
  - simpl. lia.
Qed.


Lemma proof_of_p044_change_base_safety_wit_19 : p044_change_base_safety_wit_19.
Proof.
  unfold p044_change_base_safety_wit_19.
  intros.
  pre_process.
  assert (total <= x_pre) by
    (subst total; apply base_digits_length_pos_le; lia).
  entailer!.
Qed. 

Lemma proof_of_p044_change_base_safety_wit_23 : p044_change_base_safety_wit_23.
Proof.
  unfold p044_change_base_safety_wit_23.
  intros.
  pre_process.
  pose proof (Z.rem_bound_pos x base_pre ltac:(lia) ltac:(lia)).
  entailer!.
Qed. 

Lemma proof_of_p044_change_base_entail_wit_1 : p044_change_base_entail_wit_1.
Proof.
  unfold p044_change_base_entail_wit_1.
  intros.
  pre_process.
  pose proof (base_count_state_init x_pre base_pre ltac:(lia)).
  entailer!.
Qed. 

Lemma proof_of_p044_change_base_entail_wit_2 : p044_change_base_entail_wit_2.
Proof.
  unfold p044_change_base_entail_wit_2.
  intros.
  pre_process.
  assert (Htpos : 0 < t) by lia.
  pose proof (base_count_state_step _ _ _ _ Htpos H2 H10).
  replace (t ÷ base_pre) with (t / base_pre)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  assert (Hdigits_lt : digits + 1 < INT_MAX).
  {
    unfold base_count_state in H10.
    destruct H10 as [_ [_ Hlen]].
    rewrite (base_digits_pos_step t base_pre) in Hlen by lia.
    rewrite Zlength_app in Hlen.
    change (Zlength (cons (48 + t mod base_pre) nil)) with 1 in Hlen.
    unfold base_digits_pos in Hlen.
    replace ((x_pre <=? 0)%Z) with false in Hlen by (symmetry; apply Z.leb_gt; lia).
    pose proof (base_digits_length_pos_le x_pre base_pre H0 H2).
    pose proof (Zlength_nonneg
      (if (t / base_pre <=? 0)%Z
       then nil
       else base_digits (t / base_pre) base_pre)).
    lia.
  }
  entailer!.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_p044_change_base_entail_wit_3 : p044_change_base_entail_wit_3.
Proof.
  unfold p044_change_base_entail_wit_3.
  intros.
  pre_process.
  assert (t = 0) by lia; subst t.
  pose proof (base_count_state_done _ _ _ H1 H11) as Hdigits.
  subst digits.
  sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 (Zlength (base_digits x_pre base_pre) + 1)).
  rewrite (CharArray.full_empty retval 0).
  rewrite (CharArray.undef_seg_empty retval 0).
  entailer!.
  lia.
Qed. 

Lemma proof_of_p044_change_base_entail_wit_4 : p044_change_base_entail_wit_4.
Proof.
  unfold p044_change_base_entail_wit_4.
  intros.
  pre_process.
  rewrite repeat_Z_tail by lia.
  entailer!.
Qed. 

Lemma proof_of_p044_change_base_entail_wit_5 : p044_change_base_entail_wit_5.
Proof.
  unfold p044_change_base_entail_wit_5.
  intros.
  pre_process.
  assert (i = total + 1) by lia; subst i.
  rewrite (CharArray.undef_seg_empty out (total + 1)).
  Exists (repeat_Z 0 total).
  rewrite repeat_Z_tail by (subst total; apply Zlength_nonneg).
  entailer!.
  - subst digits total.
    apply base_fill_full_state_init; lia.
  - rewrite Zlength_repeat_Z; [lia | subst total; apply Zlength_nonneg].
Qed. 

Lemma proof_of_p044_change_base_entail_wit_6 : p044_change_base_entail_wit_6.
Proof.
  unfold p044_change_base_entail_wit_6.
  intros.
  pre_process.
  Exists out_l_2.
  entailer!.
  subst digits total. apply Zlength_nonneg.
Qed. 

Lemma proof_of_p044_change_base_entail_wit_7 : p044_change_base_entail_wit_7.
Proof.
  unfold p044_change_base_entail_wit_7.
  intros.
  pre_process.
  Exists out_l_2.
  assert (Hxpos : 0 < x) by lia.
  pose proof (base_fill_full_state_positive_digits _ _ _ _ _ Hxpos H2 H11).
  replace (digits - 1 + 1) with digits by lia.
  entailer!.
Qed. 

Lemma proof_of_p044_change_base_entail_wit_8 : p044_change_base_entail_wit_8.
Proof.
  unfold p044_change_base_entail_wit_8.
  intros.
  pre_process.
  replace (x ÷ base_pre) with (x / base_pre)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  replace (Z.rem x base_pre) with (x mod base_pre)
    by (symmetry; apply Z.rem_mod_nonneg; lia).
  Exists (replace_Znth digits (signed_last_nbits (48 + x mod base_pre) 8) out_l_2).
  rewrite replace_Znth_app_l by lia.
  entailer!.
  - apply base_fill_full_state_step; lia || assumption.
  - rewrite Zlength_replace_Znth_44 by lia. lia.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_p044_change_base_return_wit_1 : p044_change_base_return_wit_1.
Proof.
  unfold p044_change_base_return_wit_1.
  intros.
  pre_process.
  assert (x = 0) by lia; subst x.
  destruct H11 as [suffix [[_ [_ [Hdigits Hsplit]]] Hout]].
  unfold base_digits_pos in Hdigits.
  replace (Z.leb 0 0) with true in Hdigits by (symmetry; apply Z.leb_le; lia).
  simpl in Hdigits. subst digits.
  simpl in Hsplit. subst suffix.
  unfold repeat_Z in Hout. simpl in Hout. subst out_l_2.
  Exists (base_digits x_pre base_pre) (Zlength (base_digits x_pre base_pre)).
  entailer!.
  - rewrite H10. entailer!.
  - apply problem_44_spec_intro; [lia | lia | reflexivity].
  - pose proof (base_digits_length_pos_le x_pre base_pre ltac:(lia) ltac:(lia)).
    lia.
  - pose proof (base_digits_nonempty x_pre base_pre) as Hnonempty.
    destruct (base_digits x_pre base_pre) eqn:Hbd; [contradiction | idtac].
    rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia.
  - intros k Hk.
    apply p044_Forall_Znth_nonzero.
    + apply base_digits_nonzero_forall; lia.
    + exact Hk.
Qed. 

Lemma proof_of_p044_change_base_return_wit_2 : p044_change_base_return_wit_2.
Proof.
  unfold p044_change_base_return_wit_2.
  intros.
  pre_process.
  subst x_pre.
  Exists ((48 :: nil) : list Z) 1.
  rewrite (CharArray.undef_seg_empty retval 2).
  entailer!.
  - change (((48 :: nil) ++ 0 :: nil)) with (48 :: 0 :: nil).
    rewrite (CharArray.full_unfold retval (1 + 1) (0 :: nil) 48).
    rewrite (CharArray.seg_unfold retval 1 (1 + 1) nil 0).
    rewrite (CharArray.seg_empty retval 2 2).
    entailer!.
  - apply problem_44_spec_zero; lia.
  - intros k Hk.
    assert (k = 0) by lia.
    subst k.
    unfold Znth.
    simpl.
    lia.
Qed. 

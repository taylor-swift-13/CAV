Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p079_decimal_to_binary Require Import p079_decimal_to_binary_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Arith.Arith.

Import naive_C_Rules.
Require Import p079_decimal_to_binary.
Local Open Scope sac.
Require Import ZArith.
Require Import String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.Ascii.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
Require Import string_bridge.
Require Export base_conversion_lib binary_digits_lib.

Local Open Scope list_scope.

(* Proof helpers moved from p079_decimal_to_binary.v so public contract files expose definitions only. *)

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
  replace (Z.leb n 0) with false by (symmetry; apply Z.leb_gt; lia).
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
    replace (Z.leb base 1) with false by (symmetry; apply Z.leb_gt; lia).
    replace (Z.leb n 0) with false by (symmetry; apply Z.leb_gt; lia).
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
  replace (Z.leb n 0) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite base_digits_equation.
  replace (Z.leb base 1) with false by (symmetry; apply Z.leb_gt; lia).
  replace (Z.leb n 0) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (Z.ltb_spec n base).
  - assert (Hdiv0 : n / base = 0) by (apply Z.div_small; lia).
    rewrite Hdiv0.
    unfold base_digits_pos.
    replace (Z.leb 0 0) with true by (symmetry; apply Z.leb_le; lia).
    rewrite Z.mod_small by lia.
    reflexivity.
  - assert (Hdivpos : 0 < n / base) by (apply Z.div_str_pos; lia).
    unfold base_digits_pos at 1.
    replace (Z.leb (n / base) 0) with false by (symmetry; apply Z.leb_gt; lia).
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
  replace (Z.leb 0 0) with true in Hlen by (symmetry; apply Z.leb_le; lia).
  rewrite Zlength_nil in Hlen.
  replace (Z.leb orig 0) with false in Hlen by (symmetry; apply Z.leb_gt; lia).
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
        replace (Z.leb orig 0) with false by (symmetry; apply Z.leb_gt; lia).
        exact Hdigits.
      * unfold base_digits_pos.
        replace (Z.leb orig 0) with false by (symmetry; apply Z.leb_gt; lia).
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
Lemma base_fill_full_state_done : forall orig base out_l,
  base_fill_full_state orig base 0 0 out_l ->
  out_l = base_digits orig base.
Proof.
  intros orig base out_l [suffix [Hstate Hout]].
  unfold base_fill_state in Hstate.
  destruct Hstate as [_ [_ [_ Hbase]]].
  unfold base_digits_pos in Hbase.
  replace (Z.leb 0 0) with true in Hbase by (symmetry; apply Z.leb_le; lia).
  simpl in Hbase.
  rewrite Hout.
  unfold repeat_Z.
  simpl.
  symmetry.
  exact Hbase.
Qed.
Lemma signed_last_nbits_char : forall r,
  0 <= r < 10 ->
  signed_last_nbits (48 + r) 8 = 48 + r.
Proof.
  intros r Hr.
  rewrite signed_last_nbits_eq by lia.
  reflexivity.
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
    replace (Z.leb base 1) with false by (symmetry; apply Z.leb_gt; lia).
    replace (Z.leb n 0) with false by (symmetry; apply Z.leb_gt; lia).
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
Lemma p079_Forall_Znth_nonzero : forall l p,
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
Lemma binary_digits_length_pos_le : forall n,
  0 < n ->
  Zlength (binary_digits n) <= n.
Proof.
  intros n Hn.
  unfold binary_digits.
  apply base_digits_length_pos_le; lia.
Qed.
Lemma binary_digits_nonempty : forall n,
  binary_digits n <> [].
Proof.
  intros n.
  unfold binary_digits.
  apply base_digits_nonempty.
Qed.
Lemma binary_count_state_init : forall orig,
  0 < orig ->
  binary_count_state orig orig 0.
Proof.
  intros orig Horig.
  unfold binary_count_state.
  apply base_count_state_init; lia.
Qed.
Lemma binary_count_state_step : forall orig t digits,
  0 < t ->
  binary_count_state orig t digits ->
  binary_count_state orig (t / 2) (digits + 1).
Proof.
  intros orig t digits Ht Hstate.
  unfold binary_count_state in *.
  apply base_count_state_step; lia || exact Hstate.
Qed.
Lemma binary_count_state_done : forall orig digits,
  0 < orig ->
  binary_count_state orig 0 digits ->
  digits = Zlength (binary_digits orig).
Proof.
  intros orig digits Horig Hstate.
  unfold binary_count_state, binary_digits in *.
  apply base_count_state_done; lia || exact Hstate.
Qed.
Lemma binary_count_state_step_safe : forall orig t digits,
  0 < orig ->
  orig < INT_MAX ->
  0 < t ->
  binary_count_state orig t digits ->
  digits + 1 < INT_MAX.
Proof.
  intros orig t digits Horig Hbound Ht [_ [Hdigits Hlen]].
  unfold binary_digits.
  unfold base_digits_pos in Hlen.
  replace (Z.leb t 0) with false in Hlen by (symmetry; apply Z.leb_gt; lia).
  replace (Z.leb orig 0) with false in Hlen by (symmetry; apply Z.leb_gt; lia).
  destruct (base_digits t 2) eqn:Hbd.
  - exfalso. apply (base_digits_nonempty t 2). exact Hbd.
  - rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg l).
    pose proof (base_digits_length_pos_le orig 2 Horig ltac:(lia)).
    lia.
Qed.
Lemma binary_fill_full_state_init : forall orig,
  0 < orig ->
  binary_fill_full_state orig orig (Zlength (binary_digits orig))
    (repeat_Z 0 (Zlength (binary_digits orig))).
Proof.
  intros orig Horig.
  unfold binary_fill_full_state, binary_digits.
  apply base_fill_full_state_init; lia.
Qed.
Lemma binary_fill_full_state_step : forall orig x digits out_l,
  0 < x ->
  0 <= digits ->
  binary_fill_full_state orig x (digits + 1) out_l ->
  binary_fill_full_state orig (x / 2) digits
    (replace_Znth digits (signed_last_nbits (48 + x mod 2) 8) out_l).
Proof.
  intros orig x digits out_l Hx Hdigits Hstate.
  unfold binary_fill_full_state in *.
  apply base_fill_full_state_step; lia || exact Hstate.
Qed.
Lemma binary_fill_full_state_done : forall orig out_l,
  binary_fill_full_state orig 0 0 out_l ->
  out_l = binary_digits orig.
Proof.
  intros orig out_l Hstate.
  unfold binary_fill_full_state, binary_digits in *.
  apply base_fill_full_state_done; exact Hstate.
Qed.
Lemma decorated_binary_digits_zero :
  decorated_binary_digits 0 = [100; 98; 48; 100; 98].
Proof.
  unfold decorated_binary_digits, binary_digits.
  rewrite base_digits_equation.
  replace (Z.leb 2 1) with false by (symmetry; apply Z.leb_gt; lia).
  replace (Z.leb 0 0) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.
Lemma problem_79_spec_intro : forall decimal out_l,
  out_l = decorated_binary_digits decimal ->
  problem_79_spec decimal out_l.
Proof.
  intros decimal out_l Hout.
  unfold problem_79_spec.
  exact Hout.
Qed.
Lemma problem_79_spec_zero :
  problem_79_spec 0 [100; 98; 48; 100; 98].
Proof.
  apply problem_79_spec_intro.
  rewrite decorated_binary_digits_zero.
  reflexivity.
Qed.
Lemma decorated_binary_digits_nonzero : forall decimal,
  0 <= decimal ->
  Forall (fun c => c <> 0) (decorated_binary_digits decimal).
Proof.
  intros decimal Hdecimal.
  unfold decorated_binary_digits, binary_digits.
  apply Forall_app; split.
  - repeat constructor; lia.
  - apply Forall_app; split.
    + destruct (Z.eq_dec decimal 0) as [-> | Hnz].
      * rewrite base_digits_equation.
        replace (Z.leb 2 1) with false by (symmetry; apply Z.leb_gt; lia).
        replace (Z.leb 0 0) with true by (symmetry; apply Z.leb_le; lia).
        repeat constructor; lia.
      * apply base_digits_nonzero_forall; lia.
    + repeat constructor; lia.
Qed.
Lemma decorated_binary_digits_Znth_nonzero : forall decimal k,
  0 <= decimal ->
  0 <= k < Zlength (decorated_binary_digits decimal) ->
  Znth k (decorated_binary_digits decimal) 0 <> 0.
Proof.
  intros decimal k Hdecimal Hk.
  eapply p079_Forall_Znth_nonzero.
  - apply decorated_binary_digits_nonzero. exact Hdecimal.
  - exact Hk.
Qed.
Lemma decimal_binary_full_state_init : forall orig,
  0 < orig ->
  decimal_binary_full_state orig orig (Zlength (binary_digits orig))
    ([100; 98] ++ repeat_Z 0 (Zlength (binary_digits orig)) ++ [100; 98]).
Proof.
  intros orig Horig.
  exists (repeat_Z 0 (Zlength (binary_digits orig))).
  split.
  - apply binary_fill_full_state_init. lia.
  - reflexivity.
Qed.
Lemma decimal_binary_full_state_step : forall orig x digits out_l,
  0 < x ->
  0 <= digits ->
  decimal_binary_full_state orig x (digits + 1) out_l ->
  decimal_binary_full_state orig (x / 2) digits
    (replace_Znth (digits + 2) (signed_last_nbits (48 + x mod 2) 8) out_l).
Proof.
  intros orig x digits out_l Hx Hdigits
    [payload [Hpayload Hout]].
  exists (replace_Znth digits (signed_last_nbits (48 + x mod 2) 8) payload).
  split.
  - apply binary_fill_full_state_step; lia || exact Hpayload.
  - rewrite Hout.
    destruct Hpayload as [suffix [[_ [_ [_ Hsplit]]] Hpayload_eq]].
    rewrite replace_Znth_app_r.
    2:{ rewrite Zlength_cons, Zlength_cons, Zlength_nil. lia. }
    replace (replace_Znth (digits + 2)
      (signed_last_nbits (48 + x mod 2) 8) [100; 98]) with [100; 98].
    2:{
      unfold replace_Znth.
      replace (Z.to_nat (digits + 2)) with (S (S (Z.to_nat digits))) by lia.
      simpl.
      destruct (Z.to_nat digits);
      reflexivity.
    }
    replace (digits + 2 - Zlength [100; 98]) with digits
      by (rewrite Zlength_cons, Zlength_cons, Zlength_nil; lia).
    rewrite replace_Znth_app_l by
      (try lia;
       rewrite Hpayload_eq;
       rewrite Zlength_app;
       rewrite Zlength_repeat_Z by lia;
       pose proof (Zlength_nonneg suffix);
       lia).
    reflexivity.
Qed.
Lemma decimal_binary_full_state_positive_digits : forall orig x digits out_l,
  0 < x ->
  decimal_binary_full_state orig x digits out_l ->
  1 <= digits.
Proof.
  intros orig x digits out_l Hx [payload [Hpayload _]].
  pose proof (base_fill_full_state_positive_digits orig 2 x digits payload
    Hx ltac:(lia) Hpayload).
  lia.
Qed.
Lemma decimal_binary_full_state_done : forall orig out_l,
  0 <= orig ->
  decimal_binary_full_state orig 0 0 out_l ->
  out_l = decorated_binary_digits orig.
Proof.
  intros orig out_l Horig [payload [Hpayload Hout]].
  pose proof (binary_fill_full_state_done orig payload Hpayload) as Hpayload_done.
  subst payload.
  unfold decorated_binary_digits.
  exact Hout.
Qed.


Lemma chararray_seg_snoc_79 : forall x lo hi l v,
  Zlength l = hi - lo ->
  ((x + hi * sizeof(CHAR)) # Char |-> v) ** CharArray.seg x lo hi l |--
  CharArray.seg x lo (hi + 1) (l ++ v :: nil).
Proof.
  intros x lo hi l.
  revert lo hi.
  induction l; intros lo hi v Hlen.
  - rewrite Zlength_nil in Hlen.
    replace hi with lo by lia.
    rewrite (CharArray.seg_empty x lo lo).
    rewrite (CharArray.seg_unfold x lo (lo + 1) nil v).
    rewrite (CharArray.seg_empty x (lo + 1) (lo + 1)).
    entailer!.
  - rewrite Zlength_cons in Hlen.
    rewrite (CharArray.seg_unfold x lo hi l a).
    rewrite <- app_comm_cons.
    rewrite (CharArray.seg_unfold x lo (hi + 1) (l ++ v :: nil) a).
    assert (Htail: Zlength l = hi - (lo + 1)) by lia.
    sep_apply (IHl (lo + 1) hi v Htail).
    entailer!.
Qed.

Lemma chararray_seg_app_79 : forall x lo mid hi l1 l2,
  Zlength l1 = mid - lo ->
  CharArray.seg x lo mid l1 ** CharArray.seg x mid hi l2 |--
  CharArray.seg x lo hi (l1 ++ l2).
Proof.
  intros x lo mid hi l1.
  revert lo mid.
  induction l1; intros lo mid l2 Hlen.
  - rewrite Zlength_nil in Hlen.
    replace mid with lo by lia.
    rewrite (CharArray.seg_empty x lo lo).
    simpl. entailer!.
  - rewrite Zlength_cons in Hlen.
    rewrite (CharArray.seg_unfold x lo mid l1 a).
    simpl.
    rewrite (CharArray.seg_unfold x lo hi (l1 ++ l2) a).
    assert (Htail: Zlength l1 = mid - (lo + 1)) by lia.
    sep_apply (IHl1 (lo + 1) mid l2 Htail).
    entailer!.
Qed.

Lemma chararray_seg_to_full_79 : forall x n l,
  CharArray.seg x 0 n l |-- CharArray.full x n l.
Proof.
  intros.
  unfold CharArray.seg, CharArray.full.
  entailer!.
Qed.

Lemma chararray_point_seg_cons_79 : forall x lo hi v l,
  ((x + lo * sizeof(CHAR)) # Char |-> v) **
    CharArray.seg x (lo + 1) hi l |--
  CharArray.seg x lo hi (v :: l).
Proof.
  intros.
  rewrite (CharArray.seg_unfold x lo hi l v).
  entailer!.
Qed.

Lemma chararray_full_join_79 : forall out total payload,
  Zlength payload = total ->
  CharArray.full out 2 (100 :: 98 :: nil) **
  CharArray.seg out 2 (total + 2) payload **
  CharArray.seg out (total + 2) (total + 5) (100 :: 98 :: 0 :: nil)
  |-- CharArray.full out (total + 5)
        ((100 :: 98 :: nil) ++ payload ++ (100 :: 98 :: 0 :: nil)).
Proof.
  intros out total payload Hpayload.
  sep_apply (CharArray.full_to_seg out 2 (100 :: 98 :: nil)).
  assert (Hprefix: Zlength (100 :: 98 :: nil) = 2 - 0)
    by (rewrite Zlength_cons, Zlength_cons, Zlength_nil; lia).
  sep_apply (chararray_seg_app_79 out 0 2 (total + 2)
    (100 :: 98 :: nil) payload Hprefix).
  assert (Hcombined:
    Zlength ((100 :: 98 :: nil) ++ payload) = (total + 2) - 0).
  { rewrite Zlength_app.
    rewrite Zlength_cons, Zlength_cons, Zlength_nil.
    lia. }
  eapply derivable1_trans with
    (y := CharArray.seg out 0 (total + 5)
            (((100 :: 98 :: nil) ++ payload) ++ (100 :: 98 :: 0 :: nil))).
  - apply (chararray_seg_app_79 out 0 (total + 2) (total + 5)
      ((100 :: 98 :: nil) ++ payload) (100 :: 98 :: 0 :: nil) Hcombined).
  - apply chararray_seg_to_full_79.
Qed.

Lemma chararray_full_join_snoc_79 : forall out total payload,
  Zlength payload = total ->
  CharArray.seg out 2 (total + 3) (payload ++ 100 :: nil) **
  CharArray.seg out (total + 3) (total + 5) (98 :: 0 :: nil) **
  CharArray.full out 2 (100 :: 98 :: nil)
  |-- CharArray.full out (total + 5)
        ((100 :: 98 :: nil) ++ payload ++ (100 :: 98 :: 0 :: nil)).
Proof.
  intros out total payload Hpayload.
  sep_apply (CharArray.full_to_seg out 2 (100 :: 98 :: nil)).
  assert (Hprefix: Zlength (100 :: 98 :: nil) = 2 - 0)
    by (rewrite Zlength_cons, Zlength_cons, Zlength_nil; lia).
  sep_apply (chararray_seg_app_79 out 0 2 (total + 3)
    (100 :: 98 :: nil) (payload ++ 100 :: nil) Hprefix).
  assert (Hcombined:
    Zlength ((100 :: 98 :: nil) ++ (payload ++ 100 :: nil)) =
      (total + 3) - 0).
  {
    rewrite !Zlength_app.
    rewrite !Zlength_cons, Zlength_nil.
    lia.
  }
  eapply derivable1_trans with
    (y := CharArray.seg out 0 (total + 5)
            (((100 :: 98 :: nil) ++ (payload ++ 100 :: nil)) ++
             (98 :: 0 :: nil))).
  - apply (chararray_seg_app_79 out 0 (total + 3) (total + 5)
      ((100 :: 98 :: nil) ++ (payload ++ 100 :: nil))
      (98 :: 0 :: nil) Hcombined).
  - replace (List.app (List.app (100 :: 98 :: nil)
                (List.app payload (100 :: nil))) (98 :: 0 :: nil))
      with (List.app (List.app (100 :: 98 :: nil) payload)
              (100 :: 98 :: 0 :: nil))
      by (simpl; rewrite <- app_assoc; reflexivity).
    apply chararray_seg_to_full_79.
Qed.

Lemma proof_of_p079_decimal_to_binary_safety_wit_24 : p079_decimal_to_binary_safety_wit_24.
Proof.
  unfold p079_decimal_to_binary_safety_wit_24.
  intros.
  pre_process.
  assert (x = 0) by lia; subst x.
  match goal with
  | Hstate: binary_count_state ?d 0 ?b |- _ =>
      pose proof (binary_count_state_done d b ltac:(lia) Hstate)
  end.
  pose proof (binary_digits_length_pos_le decimal_pre ltac:(lia)).
  entailer!; lia.
Qed. 

Lemma proof_of_p079_decimal_to_binary_safety_wit_31 : p079_decimal_to_binary_safety_wit_31.
Proof.
  unfold p079_decimal_to_binary_safety_wit_31.
  intros.
  pre_process.
  pose proof (binary_digits_length_pos_le decimal_pre ltac:(lia)).
  pose proof (Zlength_nonneg (binary_digits decimal_pre)).
  entailer!; lia.
Qed. 

Lemma proof_of_p079_decimal_to_binary_safety_wit_36 : p079_decimal_to_binary_safety_wit_36.
Proof.
  unfold p079_decimal_to_binary_safety_wit_36.
  intros.
  pre_process.
  pose proof (binary_digits_length_pos_le decimal_pre ltac:(lia)).
  pose proof (Zlength_nonneg (binary_digits decimal_pre)).
  entailer!; lia.
Qed. 

Lemma proof_of_p079_decimal_to_binary_safety_wit_39 : p079_decimal_to_binary_safety_wit_39.
Proof.
  unfold p079_decimal_to_binary_safety_wit_39.
  intros.
  pre_process.
  pose proof (binary_digits_length_pos_le decimal_pre ltac:(lia)).
  pose proof (Zlength_nonneg (binary_digits decimal_pre)).
  entailer!; lia.
Qed. 

Lemma proof_of_p079_decimal_to_binary_safety_wit_42 : p079_decimal_to_binary_safety_wit_42.
Proof.
  unfold p079_decimal_to_binary_safety_wit_42.
  intros.
  pre_process.
  pose proof (binary_digits_length_pos_le decimal_pre ltac:(lia)).
  pose proof (Zlength_nonneg (binary_digits decimal_pre)).
  entailer!; lia.
Qed. 

Lemma proof_of_p079_decimal_to_binary_safety_wit_45 : p079_decimal_to_binary_safety_wit_45.
Proof.
  unfold p079_decimal_to_binary_safety_wit_45.
  intros.
  pre_process.
  pose proof (binary_digits_length_pos_le decimal_pre ltac:(lia)).
  pose proof (Zlength_nonneg (binary_digits decimal_pre)).
  entailer!; lia.
Qed. 

Lemma proof_of_p079_decimal_to_binary_safety_wit_52 : p079_decimal_to_binary_safety_wit_52.
Proof.
  unfold p079_decimal_to_binary_safety_wit_52.
  intros.
  pre_process.
  pose proof (Z.mod_pos_bound num 2 ltac:(lia)).
  pose proof (Z.rem_bound_pos num 2 ltac:(lia) ltac:(lia)).
  entailer!; lia.
Qed. 

Lemma proof_of_p079_decimal_to_binary_entail_wit_1 : p079_decimal_to_binary_entail_wit_1.
Proof.
  unfold p079_decimal_to_binary_entail_wit_1.
  intros.
  pre_process.
  entailer!.
  apply binary_count_state_init; lia.
Qed. 

Lemma proof_of_p079_decimal_to_binary_entail_wit_2 : p079_decimal_to_binary_entail_wit_2.
Proof.
  unfold p079_decimal_to_binary_entail_wit_2.
  intros.
  pre_process.
  replace (x ÷ 2) with (x / 2)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  entailer!.
  - apply binary_count_state_step; [lia | assumption].
  - apply (binary_count_state_step_safe decimal_pre x bits); lia || assumption.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_p079_decimal_to_binary_entail_wit_3 : p079_decimal_to_binary_entail_wit_3.
Proof.
  unfold p079_decimal_to_binary_entail_wit_3.
  intros.
  pre_process.
  assert (x = 0) by lia; subst x.
  match goal with
  | Hstate: binary_count_state ?d 0 ?b |- _ =>
      pose proof (binary_count_state_done d b ltac:(lia) Hstate)
  end.
  rewrite (CharArray.seg_empty retval 2 2).
  unfold repeat_Z; simpl.
  rewrite (CharArray.full_unfold retval 2 (98 :: nil) 100).
  rewrite (CharArray.seg_unfold retval 1 2 nil 98).
  rewrite (CharArray.seg_empty retval 2 2).
  change (retval + 0) with (retval + 0 * sizeof(CHAR)).
  change (retval + match sizeof(CHAR) with
                   | 0 => 0
                   | Z.pos y' => Z.pos y'
                   | Z.neg y' => Z.neg y'
                   end) with (retval + 1 * sizeof(CHAR)).
  entailer!.
Qed. 

Lemma proof_of_p079_decimal_to_binary_entail_wit_4 : p079_decimal_to_binary_entail_wit_4.
Proof.
  unfold p079_decimal_to_binary_entail_wit_4.
  intros.
  pre_process.
  rewrite repeat_Z_tail by lia.
  replace (i + 1 + 2) with ((i + 2) + 1) by lia.
  entailer!.
Qed. 

Lemma proof_of_p079_decimal_to_binary_entail_wit_5 : p079_decimal_to_binary_entail_wit_5.
Proof.
  unfold p079_decimal_to_binary_entail_wit_5.
  intros.
  pre_process.
  assert (i = total) by lia; subst i.
  entailer!.
  unfold CharArray.undef_seg, store_undef_array.
  replace (Z.to_nat (total + 5 - (total + 2))) with 3%nat by lia.
  replace (Z.to_nat (total + 4 - (total + 2))) with 2%nat by lia.
  replace (Z.to_nat (total + 5 - (total + 4))) with 1%nat by lia.
  simpl.
  replace (total + 2 + 1 + 1) with (total + 4) by lia.
  entailer!.
Qed. 

Lemma proof_of_p079_decimal_to_binary_entail_wit_6 : p079_decimal_to_binary_entail_wit_6.
Proof.
  unfold p079_decimal_to_binary_entail_wit_6.
  intros.
  pre_process.
  entailer!.
  unfold CharArray.undef_seg, CharArray.seg, store_undef_array, store_array.
  replace (Z.to_nat (total + 4 - (total + 2))) with 2%nat by lia.
  replace (Z.to_nat (total + 3 - (total + 2))) with 1%nat by lia.
  replace (Z.to_nat (total + 4 - (total + 3))) with 1%nat by lia.
  replace (Z.to_nat (total + 5 - (total + 4))) with 1%nat by lia.
  replace (Z.to_nat (total + 5 - (total + 4 + 1))) with 0%nat by lia.
  simpl.
  replace (total + 4 + 1) with (total + 5) by lia.
  replace (total + 2 + 1) with (total + 3) by lia.
  entailer!.
Qed. 

Lemma proof_of_p079_decimal_to_binary_entail_wit_7 : p079_decimal_to_binary_entail_wit_7.
Proof.
  unfold p079_decimal_to_binary_entail_wit_7.
  intros.
  pre_process.
  rewrite (CharArray.seg_unfold out (total + 3) (total + 5) (0 :: nil) 98).
  replace (total + 3 + 1) with (total + 4) by lia.
  rewrite (CharArray.undef_seg_empty out (total + 4)).
  entailer!.
Qed. 

Lemma proof_of_p079_decimal_to_binary_entail_wit_8 : p079_decimal_to_binary_entail_wit_8.
Proof.
  unfold p079_decimal_to_binary_entail_wit_8.
  intros.
  pre_process.
  Exists (List.app (List.app (100 :: 98 :: nil) (repeat_Z 0 total))
          (100 :: 98 :: nil)).
  replace (total + 2 + 1) with (total + 3) by lia.
  rewrite (CharArray.undef_seg_empty out (total + 3)).
  entailer!.
  - assert (Hpayload: Zlength (repeat_Z 0 total) = total).
    { rewrite Zlength_repeat_Z by
        (pose proof (Zlength_nonneg (binary_digits decimal_pre)); lia).
      reflexivity. }
    sep_apply (chararray_full_join_snoc_79 out total (repeat_Z 0 total) Hpayload).
    entailer!; try (simpl; rewrite <- app_assoc; reflexivity).
  - subst bits.
    rewrite H5.
    apply decimal_binary_full_state_init; lia.
  - rewrite Zlength_app.
    change (Zlength (100 :: 98 :: nil)) with 2.
    rewrite Zlength_app.
    rewrite Zlength_repeat_Z by
      (pose proof (Zlength_nonneg (binary_digits decimal_pre)); lia).
    change (Zlength (100 :: 98 :: nil)) with 2.
    lia.
Qed. 

Lemma proof_of_p079_decimal_to_binary_entail_wit_9 : p079_decimal_to_binary_entail_wit_9.
Proof.
  unfold p079_decimal_to_binary_entail_wit_9.
  intros.
  pre_process.
  subst orig num x bits.
  Exists out_l_2.
  entailer!.
  pose proof (Zlength_nonneg (binary_digits decimal_pre)); lia.
Qed. 

Lemma proof_of_p079_decimal_to_binary_entail_wit_10 : p079_decimal_to_binary_entail_wit_10.
Proof.
  unfold p079_decimal_to_binary_entail_wit_10.
  intros.
  pre_process.
  match goal with
  | Hstate: decimal_binary_full_state orig num bits out_l_2 |- _ =>
      pose proof (decimal_binary_full_state_positive_digits orig num bits out_l_2
        ltac:(lia) Hstate)
  end.
  Exists out_l_2.
  replace (bits - 1 + 1) with bits by lia.
  entailer!; lia.
Qed. 

Lemma proof_of_p079_decimal_to_binary_entail_wit_11 : p079_decimal_to_binary_entail_wit_11.
Proof.
  unfold p079_decimal_to_binary_entail_wit_11.
  intros.
  pre_process.
  replace (num ÷ 2) with (num / 2)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  replace (Z.rem num 2) with (num mod 2)
    by (symmetry; apply Z.rem_mod_nonneg; lia).
  Exists (replace_Znth (bits + 2) (signed_last_nbits (48 + num mod 2) 8) out_l_2).
  rewrite replace_Znth_app_l by lia.
  entailer!.
  - apply decimal_binary_full_state_step; lia || assumption.
  - rewrite Zlength_replace_Znth_44 by lia. lia.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_p079_decimal_to_binary_return_wit_1 : p079_decimal_to_binary_return_wit_1.
Proof.
  unfold p079_decimal_to_binary_return_wit_1.
  intros.
  pre_process.
  assert (num = 0) by lia; subst num.
  match goal with
  | Hstate: decimal_binary_full_state orig 0 bits out_l_2 |- _ =>
      let Hcopy := fresh "Hstate_copy" in
      pose proof Hstate as Hcopy;
      destruct Hcopy as [payload [Hpayload Hout]];
      unfold binary_fill_full_state, base_fill_full_state in Hpayload;
      destruct Hpayload as [suffix [[_ [_ [Hdigits _]]] _]];
      unfold base_digits_pos in Hdigits;
      replace (Z.leb 0 0) with true in Hdigits by
        (symmetry; apply Z.leb_le; lia);
      simpl in Hdigits;
      subst bits;
      pose proof (decimal_binary_full_state_done orig out_l_2 ltac:(lia) Hstate)
        as Hdone
  end.
  Exists out_l_2 (total + 4).
  entailer!.
  - replace (total + 4 + 1) with (total + 5) by lia.
    entailer!.
  - subst orig.
    apply problem_79_spec_intro. assumption.
  - subst orig.
    pose proof (binary_digits_length_pos_le decimal_pre ltac:(lia)).
    pose proof (Zlength_nonneg (binary_digits decimal_pre)).
    lia.
  - subst orig.
    rewrite Hdone.
    intros k Hk.
    eapply decorated_binary_digits_Znth_nonzero.
    + lia.
    + rewrite <- Hdone. lia.
Qed. 

Lemma proof_of_p079_decimal_to_binary_return_wit_2 : p079_decimal_to_binary_return_wit_2.
Proof.
  unfold p079_decimal_to_binary_return_wit_2.
  intros.
  pre_process.
  subst decimal_pre.
  Exists ((100 :: 98 :: 48 :: 100 :: 98 :: nil) : list Z) 5.
  rewrite (CharArray.undef_seg_empty retval 6).
  entailer!.
  - change (List.app (100 :: 98 :: 48 :: 100 :: 98 :: nil) (0 :: nil))
      with (100 :: 98 :: 48 :: 100 :: 98 :: 0 :: nil).
    rewrite (CharArray.full_unfold retval (5 + 1)
      (98 :: 48 :: 100 :: 98 :: 0 :: nil) 100).
    rewrite (CharArray.seg_unfold retval 1 (5 + 1)
      (48 :: 100 :: 98 :: 0 :: nil) 98).
    rewrite (CharArray.seg_unfold retval 2 (5 + 1)
      (100 :: 98 :: 0 :: nil) 48).
    rewrite (CharArray.seg_unfold retval 3 (5 + 1)
      (98 :: 0 :: nil) 100).
    rewrite (CharArray.seg_unfold retval 4 (5 + 1)
      (0 :: nil) 98).
    rewrite (CharArray.seg_unfold retval 5 (5 + 1) nil 0).
    rewrite (CharArray.seg_empty retval 6 6).
    entailer!.
  - intros k Hk.
    assert (Hkn : (Z.to_nat k < 5)%nat) by lia.
    unfold Znth.
    destruct (Z.to_nat k) as [|[|[|[|[|n]]]]]; simpl; lia.
Qed. 

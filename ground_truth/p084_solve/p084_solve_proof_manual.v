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
From SimpleC.EE.CAV.ground_truth_p084_solve Require Import p084_solve_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import naive_C_Rules.
Require Import p084_solve.
Local Open Scope sac.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.Ascii.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
Require Import string_bridge.
Require Export base_conversion_lib binary_digits_lib.

Local Open Scope list_scope.

(* Proof helpers moved from p084_solve.v so public contract files expose definitions only. *)

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
Lemma decimal_sum_state_init : forall orig,
  0 <= orig ->
  decimal_sum_state orig orig 0.
Proof.
  intros orig Horig.
  unfold decimal_sum_state.
  repeat split; try lia.
  exists (Z.to_nat orig).
  split; [lia|].
  unfold decimal_digit_sum.
  reflexivity.
Qed.
Lemma decimal_digit_sum_fuel_step : forall fuel x,
  0 < x ->
  decimal_digit_sum_fuel (S fuel) x =
    Z.rem x 10 + decimal_digit_sum_fuel fuel (Z.quot x 10).
Proof.
  intros fuel x Hx.
  simpl.
  replace (Z.leb x 0) with false by (symmetry; apply Z.leb_gt; lia).
  reflexivity.
Qed.
Lemma decimal_sum_state_step : forall orig x sum,
  0 < x ->
  decimal_sum_state orig x sum ->
  decimal_sum_state orig (x / 10) (sum + x mod 10).
Proof.
  intros orig x sum Hx [Hx_nonneg [Hsum [Hbound Hstate]]].
  unfold decimal_sum_state.
  repeat split.
  - apply Z.div_pos; lia.
  - pose proof (Z.mod_pos_bound x 10 ltac:(lia)).
    lia.
  - assert (x = 10 * (x / 10) + x mod 10) by (apply Z.div_mod; lia).
    assert (x / 10 <= 10 * (x / 10)).
    { pose proof (Z.div_pos x 10 ltac:(lia) ltac:(lia)). nia. }
    lia.
  - destruct Hstate as [fuel [Hfuel Hstate]].
    destruct fuel as [|fuel']; [lia|].
    exists fuel'.
    split.
    + rewrite Z2Nat.inj_div by lia.
      apply Nat.lt_succ_r.
      eapply Nat.lt_le_trans.
      * apply Nat.div_lt; lia.
      * exact Hfuel.
    + rewrite <- Hstate.
      rewrite decimal_digit_sum_fuel_step by lia.
      rewrite Z.quot_div_nonneg by lia.
      rewrite Z.rem_mod_nonneg by lia.
      lia.
Qed.
Lemma decimal_sum_state_sum_bound : forall orig x sum,
  0 <= orig ->
  orig <= 10000 ->
  decimal_sum_state orig x sum ->
  sum <= 10000.
Proof.
  intros orig x sum Horig Horig_bound [Hx [Hsum [Hbound _]]].
  lia.
Qed.
Lemma decimal_digit_sum_fuel_zero : forall fuel,
  decimal_digit_sum_fuel fuel 0 = 0.
Proof.
  destruct fuel; reflexivity.
Qed.
Lemma decimal_sum_state_done : forall orig sum,
  decimal_sum_state orig 0 sum ->
  decimal_sum_value orig sum.
Proof.
  intros orig sum [_ [_ [_ [fuel [_ Hstate]]]]].
  unfold decimal_sum_value.
  change (Z.to_nat 0) with 0%nat in Hstate.
  rewrite decimal_digit_sum_fuel_zero in Hstate.
  lia.
Qed.
Lemma problem_84_spec_intro : forall N out_l sum,
  0 <= N ->
  decimal_sum_value N sum ->
  out_l = binary_digits sum ->
  problem_84_spec N out_l.
Proof.
  intros N out_l sum _ Hsum Hout.
  subst out_l.
  unfold problem_84_spec, decimal_sum_value, binary_digits in *.
  subst sum.
  reflexivity.
Qed.
Lemma problem_84_spec_zero :
  problem_84_spec 0 [48].
Proof.
  apply problem_84_spec_intro with (sum := 0).
  - lia.
  - unfold decimal_sum_value, decimal_digit_sum.
    reflexivity.
  - unfold binary_digits.
    rewrite base_digits_equation.
    replace (Z.leb 2 1) with false by (symmetry; apply Z.leb_gt; lia).
    replace (Z.leb 0 0) with true by (symmetry; apply Z.leb_le; lia).
    reflexivity.
Qed.
Lemma Forall_Znth_nonzero : forall l p,
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
Lemma binary_digits_nonzero_forall : forall n,
  0 <= n ->
  Forall (fun c => c <> 0) (binary_digits n).
Proof.
  intros n Hn.
  unfold binary_digits.
  destruct (Z.eq_dec n 0) as [-> | Hnz].
  - rewrite base_digits_equation.
    replace (Z.leb 2 1) with false by (symmetry; apply Z.leb_gt; lia).
    replace (Z.leb 0 0) with true by (symmetry; apply Z.leb_le; lia).
    constructor; [lia | constructor].
  - apply base_digits_nonzero_forall; lia.
Qed.
Lemma binary_digits_Znth_nonzero : forall n k,
  0 <= n ->
  0 <= k < Zlength (binary_digits n) ->
  Znth k (binary_digits n) 0 <> 0.
Proof.
  intros n k Hn Hk.
  eapply Forall_Znth_nonzero.
  - apply binary_digits_nonzero_forall; lia.
  - exact Hk.
Qed.


Lemma proof_of_p084_solve_safety_wit_16 : p084_solve_safety_wit_16.
Proof.
  unfold p084_solve_safety_wit_16.
  intros.
  pre_process.
  pose proof (Z.rem_bound_pos x 10 ltac:(lia) ltac:(lia)).
  entailer!.
Qed. 

Lemma proof_of_p084_solve_safety_wit_36 : p084_solve_safety_wit_36.
Proof.
  unfold p084_solve_safety_wit_36.
  intros.
  pre_process.
  assert (total <= num) by
    (subst total; apply binary_digits_length_pos_le; lia).
  entailer!.
Qed. 

Lemma proof_of_p084_solve_safety_wit_40 : p084_solve_safety_wit_40.
Proof.
  unfold p084_solve_safety_wit_40.
  intros.
  pre_process.
  pose proof (Z.rem_bound_pos num 2 ltac:(lia) ltac:(lia)).
  entailer!.
Qed. 

Lemma proof_of_p084_solve_entail_wit_1 : p084_solve_entail_wit_1.
Proof.
  unfold p084_solve_entail_wit_1.
  intros.
  pre_process.
  entailer!.
  apply decimal_sum_state_init; lia.
Qed. 

Lemma proof_of_p084_solve_entail_wit_2 : p084_solve_entail_wit_2.
Proof.
  unfold p084_solve_entail_wit_2.
  intros.
  pre_process.
  replace (x ÷ 10) with (x / 10)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  replace (Z.rem x 10) with (x mod 10)
    by (symmetry; apply Z.rem_mod_nonneg; lia).
  entailer!.
  - apply decimal_sum_state_step; lia || assumption.
  - apply decimal_sum_state_sum_bound with (orig := N_pre) (x := x / 10); try lia.
    apply decimal_sum_state_step; lia || assumption.
  - pose proof (Z.mod_pos_bound x 10 ltac:(lia)); lia.
  - assert (x / 10 <= x).
    { apply Z.div_le_upper_bound; lia. }
    lia.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_p084_solve_entail_wit_3 : p084_solve_entail_wit_3.
Proof.
  unfold p084_solve_entail_wit_3.
  intros.
  pre_process.
  assert (x = 0) by lia; subst x.
  entailer!.
  apply decimal_sum_state_done; assumption.
Qed. 

Lemma proof_of_p084_solve_entail_wit_4 : p084_solve_entail_wit_4.
Proof.
  unfold p084_solve_entail_wit_4.
  intros.
  pre_process.
  subst bits.
  entailer!.
  apply binary_count_state_init; lia.
Qed. 

Lemma proof_of_p084_solve_entail_wit_5 : p084_solve_entail_wit_5.
Proof.
  unfold p084_solve_entail_wit_5.
  intros.
  pre_process.
  replace (t ÷ 2) with (t / 2)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  entailer!.
  - apply binary_count_state_step; lia || assumption.
  - apply binary_count_state_step_safe with (orig := num) (t := t); lia || assumption.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_p084_solve_entail_wit_6 : p084_solve_entail_wit_6.
Proof.
  unfold p084_solve_entail_wit_6.
  intros.
  pre_process.
  assert (t = 0) by lia; subst t.
  rewrite (CharArray.full_empty retval 0).
  entailer!.
  - unfold CharArray.undef_full, CharArray.undef_seg.
    unfold store_undef_array.
    replace (bits + 1 - 0) with (bits + 1) by lia.
    entailer!.
  - apply binary_count_state_done; lia || assumption.
Qed. 

Lemma proof_of_p084_solve_entail_wit_7 : p084_solve_entail_wit_7.
Proof.
  unfold p084_solve_entail_wit_7.
  intros.
  pre_process.
  rewrite repeat_Z_tail by lia.
  entailer!.
Qed. 

Lemma proof_of_p084_solve_entail_wit_8 : p084_solve_entail_wit_8.
Proof.
  unfold p084_solve_entail_wit_8.
  intros.
  pre_process.
  assert (i = total + 1) by lia; subst i.
  rewrite (CharArray.undef_seg_empty out (total + 1)).
  Exists (repeat_Z 0 total).
  entailer!.
  - rewrite naive_C_Rules.repeat_Z_tail
      by (pose proof (Zlength_nonneg (binary_digits num)); lia).
    unfold naive_C_Rules.repeat_Z, repeat_Z.
    entailer!.
  - subst bits. subst total. apply binary_fill_full_state_init; lia.
  - rewrite Zlength_repeat_Z by
      (pose proof (Zlength_nonneg (binary_digits num)); lia).
    lia.
Qed. 

Lemma proof_of_p084_solve_entail_wit_9 : p084_solve_entail_wit_9.
Proof.
  unfold p084_solve_entail_wit_9.
  intros.
  pre_process.
  subst sum.
  subst orig.
  Exists out_l_2.
  entailer!.
  all: try assumption;
    pose proof (Zlength_nonneg (binary_digits num)); lia.
Qed. 

Lemma proof_of_p084_solve_entail_wit_10 : p084_solve_entail_wit_10.
Proof.
  unfold p084_solve_entail_wit_10.
  intros.
  pre_process.
  Exists out_l_2.
  entailer!.
  - replace (bits - 1 + 1) with bits by lia.
    assumption.
  - pose proof (base_fill_full_state_positive_digits orig 2 num bits out_l_2
      ltac:(lia) ltac:(lia) H14).
    lia.
Qed. 

Lemma proof_of_p084_solve_entail_wit_11 : p084_solve_entail_wit_11.
Proof.
  unfold p084_solve_entail_wit_11.
  intros.
  pre_process.
  replace (num ÷ 2) with (num / 2)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  replace (Z.rem num 2) with (num mod 2)
    by (symmetry; apply Z.rem_mod_nonneg; lia).
  Exists (replace_Znth bits (signed_last_nbits (48 + num mod 2) 8) out_l_2).
  rewrite replace_Znth_app_l by lia.
  entailer!.
  - apply binary_fill_full_state_step; lia || assumption.
  - rewrite Zlength_replace_Znth_44 by lia. lia.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_p084_solve_return_wit_1 : p084_solve_return_wit_1.
Proof.
  unfold p084_solve_return_wit_1.
  intros.
  pre_process.
  assert (num = 0) by lia; subst num.
  unfold binary_fill_full_state in H14.
  destruct H14 as [suffix [[_ [_ [Hdigits Hsplit]]] Hout]].
  unfold base_digits_pos in Hdigits.
  replace (Z.leb 0 0) with true in Hdigits by (symmetry; apply Z.leb_le; lia).
  simpl in Hdigits. subst bits.
  simpl in Hsplit. subst suffix.
  unfold repeat_Z in Hout. simpl in Hout. subst out_l_2.
  Exists (binary_digits orig) (Zlength (binary_digits orig)).
  replace (Zlength (binary_digits orig) + 1) with (total + 1) by lia.
  entailer!.
  - apply problem_84_spec_intro with (sum := orig); try lia.
    + match goal with
      | Hval: decimal_sum_value N_pre ?s,
        Hs: ?s = orig |- _ => rewrite <- Hs; exact Hval
      end.
    + reflexivity.
  - pose proof (binary_digits_length_pos_le orig ltac:(lia)).
    lia.
  - pose proof (binary_digits_nonempty orig) as Hnonempty.
    destruct (binary_digits orig) eqn:Hbd; [contradiction | idtac].
    rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia.
  - intros k Hk.
    apply binary_digits_Znth_nonzero; lia.
Qed. 

Lemma proof_of_p084_solve_return_wit_2 : p084_solve_return_wit_2.
Proof.
  unfold p084_solve_return_wit_2.
  intros.
  pre_process.
  subst sum.
  Exists ((48 :: nil) : list Z) 1.
  rewrite (CharArray.undef_seg_empty retval 2).
  entailer!.
  - change (List.app (48 :: nil) (0 :: nil)) with (48 :: 0 :: nil).
    rewrite (CharArray.full_unfold retval (1 + 1) (0 :: nil) 48).
    rewrite (CharArray.seg_unfold retval 1 (1 + 1) nil 0).
    rewrite (CharArray.seg_empty retval 2 2).
    entailer!.
  - apply problem_84_spec_intro with (sum := 0); try lia.
    + assumption.
    + unfold binary_digits.
      rewrite base_digits_equation.
      replace (Z.leb 2 1) with false by (symmetry; apply Z.leb_gt; lia).
      replace (Z.leb 0 0) with true by (symmetry; apply Z.leb_le; lia).
      reflexivity.
  - intros k Hk.
    assert (k = 0) by lia.
    subst k.
    unfold Znth; simpl; lia.
Qed. 

Lemma proof_of_p084_solve_return_wit_3 : p084_solve_return_wit_3.
Proof.
  unfold p084_solve_return_wit_3.
  intros.
  pre_process.
  subst N_pre.
  Exists ((48 :: nil) : list Z) 1.
  rewrite (CharArray.undef_seg_empty retval 2).
  entailer!.
  - change (List.app (48 :: nil) (0 :: nil)) with (48 :: 0 :: nil).
    rewrite (CharArray.full_unfold retval (1 + 1) (0 :: nil) 48).
    rewrite (CharArray.seg_unfold retval 1 (1 + 1) nil 0).
    rewrite (CharArray.seg_empty retval 2 2).
    entailer!.
  - intros k Hk.
    assert (k = 0) by lia.
    subst k.
    unfold Znth; simpl; lia.
Qed. 

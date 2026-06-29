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
From SimpleC.EE Require Import p155_even_odd_count_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Lists.List Coq.Strings.Ascii Coq.ZArith.ZArith Coq.Arith.Arith.

Import naive_C_Rules.
Require Import p155_even_odd_count.
Local Open Scope sac.
Require Import Coq.ZArith.Zquot.
Require Import Lia.
From AUXLib Require Import ListLib.

Local Open Scope list_scope.

(* Proof helpers moved from p155_even_odd_count.v so public contract files expose definitions only. *)

Lemma c_digits_fuel_to_digits_fuel_nonzero : forall fuel n,
  0 <= n ->
  c_digits_fuel fuel n = to_digits_fuel_nonzero fuel n.
Proof.
  induction fuel as [|fuel IH]; intros n Hn; simpl; [reflexivity|].
  rewrite Z.abs_eq by lia.
  destruct (n =? 0) eqn:Hzero; [reflexivity|].
  rewrite Z.rem_mod_nonneg by lia.
  rewrite Z.quot_div_nonneg by lia.
  rewrite IH by (apply Z.div_pos; lia).
  reflexivity.
Qed.
Lemma to_digits_fuel_nonzero_abs : forall fuel n,
  to_digits_fuel_nonzero fuel (Z.abs n) = to_digits_fuel_nonzero fuel n.
Proof.
  destruct fuel as [|fuel]; intros n; simpl; [reflexivity|].
  rewrite Z.abs_eq by apply Z.abs_nonneg.
  reflexivity.
Qed.
Lemma c_digits_to_digits : forall n,
  c_digits n = to_digits n.
Proof.
  intros n.
  unfold c_digits, to_digits.
  destruct (Z.abs n =? 0) eqn:Habs; [reflexivity|].
  rewrite c_digits_fuel_to_digits_fuel_nonzero by apply Z.abs_nonneg.
  apply to_digits_fuel_nonzero_abs.
Qed.
Lemma count_digits_c_to_count_digits_acc : forall digits even odd,
  (forall d, In d digits -> 0 <= d) ->
  count_digits_c digits (Z.of_nat even) (Z.of_nat odd) =
  let '(even', odd') := count_digits_acc digits (even, odd) in
  (Z.of_nat even', Z.of_nat odd').
Proof.
  induction digits as [|d rest IH]; intros even odd Hnonneg; simpl.
  - reflexivity.
  - assert (Hd_nonneg : 0 <= d) by (apply Hnonneg; simpl; auto).
    rewrite Z.rem_mod_nonneg by lia.
    rewrite Zmod_odd.
    rewrite <- Z.negb_even.
    destruct (Z.even d) eqn:Heven.
    + simpl.
      replace (Z.of_nat even + 1) with (Z.of_nat (S even)) by lia.
      apply IH.
      intros x Hx. apply Hnonneg. simpl. auto.
    + simpl.
      replace (Z.of_nat odd + 1) with (Z.of_nat (S odd)) by lia.
      apply IH.
      intros x Hx. apply Hnonneg. simpl. auto.
Qed.
Lemma c_digits_fuel_nonnegative : forall fuel n d,
  0 <= n ->
  In d (c_digits_fuel fuel n) ->
  0 <= d.
Proof.
  induction fuel as [|fuel IH]; intros n d Hn Hin; simpl in Hin; [contradiction|].
  rewrite Z.abs_eq in Hin by lia.
  destruct (n =? 0) eqn:Hzero; [contradiction|].
  simpl in Hin.
  destruct Hin as [Hd | Hin].
  - subst d. apply Z.rem_bound_pos; lia.
  - apply IH in Hin.
    + exact Hin.
    + rewrite Z.quot_div_nonneg by lia.
      apply Z.div_pos; lia.
Qed.
Lemma c_digits_nonnegative : forall n d,
  In d (c_digits n) ->
  0 <= d.
Proof.
  intros n d Hin.
  unfold c_digits in Hin.
  destruct (Z.abs n =? 0) eqn:Habs.
  - simpl in Hin. destruct Hin as [-> | []]. lia.
  - eapply c_digits_fuel_nonnegative; eauto.
    apply Z.abs_nonneg.
Qed.
Lemma count_result_c_to_even_odd_count_impl : forall num,
  count_result_c num =
  let '(even, odd) := even_odd_count_impl num in
  (Z.of_nat even, Z.of_nat odd).
Proof.
  intros num.
  unfold count_result_c, even_odd_count_impl.
  rewrite <- c_digits_to_digits.
  change 0 with (Z.of_nat O).
  apply count_digits_c_to_count_digits_acc.
  apply c_digits_nonnegative.
Qed.
Lemma c_digits_fuel_length_bound : forall fuel n,
  Zlength (c_digits_fuel fuel n) <= Z.of_nat fuel.
Proof.
  intros fuel.
  induction fuel as [|fuel IH]; intros n; simpl; [rewrite Zlength_nil; lia|].
  destruct (Z.abs n =? 0).
  - rewrite Zlength_nil. lia.
  - rewrite Zlength_cons.
    pose proof (IH (Z.quot (Z.abs n) 10)).
    lia.
Qed.
Lemma digit_count_state_init_zero : forall num,
  Z.abs num = 0 ->
  digit_count_state num 0 1 0.
Proof.
  intros num Habs.
  unfold digit_count_state, count_result_c, c_digits.
  rewrite Habs.
  simpl.
  repeat split; try lia.
  exists O.
  split; [left; lia|].
  split; [reflexivity|].
  rewrite Zlength_nil; lia.
Qed.
Lemma digit_count_state_init_nonzero : forall num,
  0 < Z.abs num ->
  digit_count_state num (Z.abs num) 0 0.
Proof.
  intros num Habs.
  unfold digit_count_state, count_result_c, c_digits.
  destruct (Z.abs num =? 0) eqn:Hz; [apply Z.eqb_eq in Hz; lia|].
  repeat split; try lia.
  exists (Z.to_nat (Z.abs num) + 1)%nat.
  split.
  - right.
    rewrite Nat2Z.inj_add, Z2Nat.id by lia.
    simpl.
    lia.
  - split; [reflexivity|].
    pose proof (c_digits_fuel_length_bound
      (Z.to_nat (Z.abs num) + 1)%nat (Z.abs num)).
    rewrite Nat2Z.inj_add in H.
    rewrite Z2Nat.id in H by lia.
    simpl in H.
    lia.
Qed.
Lemma c_digits_fuel_step : forall fuel w,
  0 < w ->
  w < Z.of_nat fuel ->
  c_digits_fuel fuel w =
    Z.rem w 10 :: c_digits_fuel (Nat.pred fuel) (Z.quot w 10).
Proof.
  intros fuel w Hw Hfuel.
  destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
  simpl.
  rewrite Z.abs_eq by lia.
  destruct (w =? 0) eqn:Hz; [apply Z.eqb_eq in Hz; lia|].
  reflexivity.
Qed.
Lemma Zquot_10_lt_self : forall w,
  0 < w ->
  Z.quot w 10 < w.
Proof.
  intros w Hw.
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_lt_upper_bound; lia.
Qed.
Lemma digit_count_state_odd_next_bound : forall num w even odd bound,
  digit_count_state num w even odd ->
  0 < w ->
  Z.abs num + 1 < bound ->
  odd + 1 < bound.
Proof.
  intros num w even odd bound Hstate Hw Hbound.
  unfold digit_count_state in Hstate.
  destruct Hstate as [_ [He_lo [Ho_lo [fuel [Hfuel [_ Hlen]]]]]].
  assert (Hfuel_pos : w < Z.of_nat fuel) by lia.
  rewrite (c_digits_fuel_step fuel w Hw Hfuel_pos) in Hlen.
  rewrite Zlength_cons in Hlen.
  unfold Zabs in Hlen.
  pose proof (Zlength_nonneg (c_digits_fuel (Nat.pred fuel) (w ÷ 10))).
  lia.
Qed.
Lemma digit_count_state_even_next_bound : forall num w even odd bound,
  digit_count_state num w even odd ->
  0 < w ->
  Z.abs num + 1 < bound ->
  even + 1 < bound.
Proof.
  intros num w even odd bound Hstate Hw Hbound.
  unfold digit_count_state in Hstate.
  destruct Hstate as [_ [He_lo [Ho_lo [fuel [Hfuel [_ Hlen]]]]]].
  assert (Hfuel_pos : w < Z.of_nat fuel) by lia.
  rewrite (c_digits_fuel_step fuel w Hw Hfuel_pos) in Hlen.
  rewrite Zlength_cons in Hlen.
  unfold Zabs in Hlen.
  pose proof (Zlength_nonneg (c_digits_fuel (Nat.pred fuel) (w ÷ 10))).
  lia.
Qed.
Lemma digit_count_state_step_odd : forall num w even odd d,
  digit_count_state num w even odd ->
  0 < w ->
  d = Z.rem w 10 ->
  Z.rem d 2 = 1 ->
  digit_count_state num (Z.quot w 10) even (odd + 1).
Proof.
  intros num w even odd d Hstate Hw Hd Hodd.
  unfold digit_count_state in *.
  destruct Hstate as [Hw_nonneg [He_lo [Ho_lo [fuel [Hfuel [Hrun Hlen]]]]]].
  assert (Hfuel_pos : w < Z.of_nat fuel) by lia.
  rewrite (c_digits_fuel_step fuel w Hw Hfuel_pos) in Hrun.
  rewrite (c_digits_fuel_step fuel w Hw Hfuel_pos) in Hlen.
  subst d.
  destruct (Z.rem (Z.rem w 10) 2 =? 1) eqn:Hpar;
    [| apply Z.eqb_neq in Hpar; lia].
  simpl in Hrun.
  rewrite Hpar in Hrun.
  split.
  - rewrite Z.quot_div_nonneg by lia.
    apply Z.div_pos; lia.
  - split; [lia|].
    split; [lia|].
    exists (Nat.pred fuel).
    split.
    + destruct (Z.eq_dec (Z.quot w 10) 0) as [Hzero | Hnz].
      * left; lia.
      * right.
        destruct fuel as [|fuel']; [simpl in Hfuel_pos; lia|].
        simpl.
        rewrite Nat2Z.inj_succ in Hfuel_pos.
        pose proof (Zquot_10_lt_self w Hw).
        lia.
    + split; [exact Hrun|].
      rewrite Zlength_cons in Hlen.
      lia.
Qed.
Lemma digit_count_state_step_even : forall num w even odd d,
  digit_count_state num w even odd ->
  0 < w ->
  d = Z.rem w 10 ->
  Z.rem d 2 <> 1 ->
  digit_count_state num (Z.quot w 10) (even + 1) odd.
Proof.
  intros num w even odd d Hstate Hw Hd Heven.
  unfold digit_count_state in *.
  destruct Hstate as [Hw_nonneg [He_lo [Ho_lo [fuel [Hfuel [Hrun Hlen]]]]]].
  assert (Hfuel_pos : w < Z.of_nat fuel) by lia.
  rewrite (c_digits_fuel_step fuel w Hw Hfuel_pos) in Hrun.
  rewrite (c_digits_fuel_step fuel w Hw Hfuel_pos) in Hlen.
  subst d.
  destruct (Z.rem (Z.rem w 10) 2 =? 1) eqn:Hpar;
    [apply Z.eqb_eq in Hpar; lia|].
  simpl in Hrun.
  rewrite Hpar in Hrun.
  split.
  - rewrite Z.quot_div_nonneg by lia.
    apply Z.div_pos; lia.
  - split; [lia|].
    split; [lia|].
    exists (Nat.pred fuel).
    split.
    + destruct (Z.eq_dec (Z.quot w 10) 0) as [Hzero | Hnz].
      * left; lia.
      * right.
        destruct fuel as [|fuel']; [simpl in Hfuel_pos; lia|].
        simpl.
        rewrite Nat2Z.inj_succ in Hfuel_pos.
        pose proof (Zquot_10_lt_self w Hw).
        lia.
    + split; [exact Hrun|].
      rewrite Zlength_cons in Hlen.
      lia.
Qed.
Lemma digit_count_state_final_spec : forall num even odd,
  digit_count_state num 0 even odd ->
  problem_155_spec num [even; odd].
Proof.
  intros num even odd Hstate.
  unfold digit_count_state in Hstate.
  destruct Hstate as [_ [Heven_nonneg [Hodd_nonneg [fuel [_ [Hrun _]]]]]].
  unfold problem_155_spec.
  exists (Z.to_nat even), (Z.to_nat odd).
  split.
  - rewrite Z2Nat.id by lia.
    rewrite Z2Nat.id by lia.
    reflexivity.
  - unfold problem_155_spec.
    pose proof (count_result_c_to_even_odd_count_impl num) as Horig.
    destruct (even_odd_count_impl num) as [even_nat odd_nat] eqn:Himpl.
    destruct fuel; simpl in Hrun; symmetry in Hrun.
    + rewrite Hrun in Horig.
      injection Horig as He Ho.
      apply f_equal with (f := Z.to_nat) in He.
      apply f_equal with (f := Z.to_nat) in Ho.
      rewrite Nat2Z.id in He, Ho.
      rewrite He, Ho.
      reflexivity.
    + rewrite Hrun in Horig.
      injection Horig as He Ho.
      apply f_equal with (f := Z.to_nat) in He.
      apply f_equal with (f := Z.to_nat) in Ho.
      rewrite Nat2Z.id in He, Ho.
      rewrite He, Ho.
      reflexivity.
Qed.


Lemma proof_of_abs_return_wit_1 : abs_return_wit_1.
Proof. pre_process. Qed.

Lemma proof_of_abs_return_wit_2 : abs_return_wit_2.
Proof. pre_process. Qed.

Lemma proof_of_p155_even_odd_count_entail_wit_1_1 : p155_even_odd_count_entail_wit_1_1.
Proof.
  pre_process.
  entailer!.
  subst retval.
  unfold Zabs in *.
  apply digit_count_state_init_nonzero.
  pose proof (Z.abs_nonneg num_pre).
  lia.
Qed.

Lemma proof_of_p155_even_odd_count_entail_wit_1_2 : p155_even_odd_count_entail_wit_1_2.
Proof.
  pre_process.
  entailer!.
  subst retval.
  apply digit_count_state_init_zero.
  unfold Zabs in *.
  lia.
Qed.

Lemma proof_of_p155_even_odd_count_entail_wit_2 : p155_even_odd_count_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  - replace (w mod 10) with (Z.rem w 10) in * by
      (apply Z.rem_mod_nonneg; lia).
    eapply digit_count_state_step_odd.
    + exact H11.
    + lia.
    + reflexivity.
    + exact H.
  - apply digit_count_state_odd_next_bound with (num := num_pre) (w := w) (even := n2); try assumption.
    unfold Zabs in *; lia.
Qed.

Lemma proof_of_p155_even_odd_count_entail_wit_3 : p155_even_odd_count_entail_wit_3.
Proof.
  pre_process.
  entailer!.
  - replace (w mod 10) with (Z.rem w 10) in * by
      (apply Z.rem_mod_nonneg; lia).
    eapply digit_count_state_step_even.
    + exact H11.
    + lia.
    + reflexivity.
    + exact H.
  - apply digit_count_state_even_next_bound with (num := num_pre) (w := w) (odd := n1); try assumption.
    unfold Zabs in *; lia.
Qed.

Lemma proof_of_p155_even_odd_count_entail_wit_4_1 : p155_even_odd_count_entail_wit_4_1.
Proof.
  pre_process.
  entailer!.
  - pose proof (Zquot_10_lt_self w H3).
    lia.
  - rewrite Z.quot_div_nonneg by lia.
    apply Z.div_pos; lia.
Qed.

Lemma proof_of_p155_even_odd_count_entail_wit_4_2 : p155_even_odd_count_entail_wit_4_2.
Proof.
  pre_process.
  entailer!.
  - pose proof (Zquot_10_lt_self w H3).
    lia.
  - rewrite Z.quot_div_nonneg by lia.
    apply Z.div_pos; lia.
Qed.

Lemma proof_of_p155_even_odd_count_return_wit_1 : p155_even_odd_count_return_wit_1.
Proof.
  pre_process.
  replace w with 0 in * by lia.
  Exists (n2 :: n1 :: nil) 2 retval_2.
  entailer!.
  - sep_apply (IntArray.seg_single retval_2 1 n1).
    sep_apply (IntArray.seg_single retval_2 0 n2).
    sep_apply (IntArray.seg_merge_to_seg retval_2 0 1 2); [ | lia].
    sep_apply (IntArray.seg_to_full retval_2 0 2).
    replace (retval_2 + 0 * sizeof (INT)) with retval_2 by lia.
    replace (2 - 0) with 2 by lia.
    entailer!.
  - apply digit_count_state_final_spec.
    assumption.
Qed.

(* spec/84 *)
(* def solve(N):
"""Given a positive integer N, return the total sum of its digits in binary.

Example
For N = 1000, the sum of digits will be 1 the output should be "1".
For N = 150, the sum of digits will be 6 the output should be "110".
For N = 147, the sum of digits will be 12 the output should be "1100".

Variables:
@N integer
Constraints: 0 ≤ N ≤ 10000.
Output:
a string of binary number
""" *)
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

(*
  辅助函数 1.1: 一个带有“燃料”的、用于计算十进制各位数字之和的函数。
  递归在 fuel 参数上是结构性的，因此 Coq 可以接受这个定义。
*)
Fixpoint sum_decimal_digits_aux (fuel n : nat) : nat :=
  match fuel with
  | 0 => 0 (* 燃料耗尽，停止 *)
  | S f' => (* 还有燃料，继续计算 *)
    match n with
    | 0 => 0
    | _ => (n mod 10) + sum_decimal_digits_aux f' (n / 10)
    end
  end.

(*
  主函数 1: 计算自然数 N 的十进制各位数字之和。
  我们提供 N 本身作为初始燃料，这足以确保计算完成。
*)
Definition sum_decimal_digits (n : nat) : nat :=
  sum_decimal_digits_aux n n.

(*
  辅助函数 2.1: 一个带有“燃料”的、用于将正整数转为二进制字符串的函数。
  同样，递归在 fuel 上是结构性的。这个辅助函数假定 n > 0。
*)
Fixpoint nat_to_binary_string_pos_aux (fuel n : nat) : string :=
  match fuel with
  | 0 => "" (* 燃料耗尽 *)
  | S f' =>
      if Nat.eqb n 0 then ""
      else nat_to_binary_string_pos_aux f' (n / 2) ++ (if Nat.eqb (n mod 2) 0 then "0" else "1")
  end.

(*
  主函数 2: 将自然数 N 转换为其二进制表示的字符串。
  这里我们特殊处理 N=0 的情况，并为正数调用辅助函数。
*)
Definition nat_to_binary_string (n : nat) : string :=
  if Nat.eqb n 0 then "0"
  else nat_to_binary_string_pos_aux n n.

Definition solve_impl (N : nat) : string :=
  nat_to_binary_string (sum_decimal_digits N).



Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
Require Import string_bridge.
Require Export base_conversion_lib binary_digits_lib.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition problem_84_pre (N : Z) : Prop :=
  0 <= N <= 10 * 1000.

Fixpoint decimal_digit_sum_fuel (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      if Z.leb n 0 then 0 else Z.rem n 10 + decimal_digit_sum_fuel fuel' (Z.quot n 10)
  end.

Definition decimal_digit_sum (n : Z) : Z :=
  decimal_digit_sum_fuel (Z.to_nat n) n.

Definition problem_84_spec (N : Z) (output : list Z) : Prop :=
  output = base_digits (decimal_digit_sum N) 2.

Definition decimal_sum_value (orig sum : Z) : Prop :=
  sum = decimal_digit_sum orig.

Definition decimal_sum_state (orig x sum : Z) : Prop :=
  0 <= x /\
  0 <= sum /\
  sum + x <= orig /\
  exists fuel,
    (Z.to_nat x <= fuel)%nat /\
    sum + decimal_digit_sum_fuel fuel x =
      decimal_digit_sum orig.
Local Open Scope nat_scope.
Local Open Scope Z_scope.


(* Ground-truth proof helpers from the current list-Z base-conversion proof. *)
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



(* Binary-state wrappers for base 2. *)
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
  replace (x <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
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
    replace (2 <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
    replace (0 <=? 0) with true by (symmetry; apply Z.leb_le; lia).
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
    replace (2 <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
    replace (0 <=? 0) with true by (symmetry; apply Z.leb_le; lia).
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

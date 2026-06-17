(* spec/65 *)
(* def circular_shift(x, shift):
"""Circular shift the digits of the integer x, shift the digits right by shift
and return the result as a string.
If shift > number of digits, return digits reversed.
>>> circular_shift(12, 1)
"21"
>>> circular_shift(12, 2)
"12"
""" *)
(* 导入所需的标准库 *)
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

Fixpoint to_digits_fuel (n fuel : nat) : list nat :=
  match fuel with
  | O => []
  | S fuel' =>
      if (n <? 10)%nat then
        [n]
      else
        (to_digits_fuel (n / 10) fuel') ++ [n mod 10]
  end.

Definition to_digits (n : nat) : list nat :=
  if (n =? 0)%nat then
    [0]
  else
    to_digits_fuel n n.

Definition digit_to_string (d : nat) : string :=
  match d with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9"
  | _ => ""
  end.

Fixpoint from_digits_to_string (l : list nat) : string :=
  match l with
  | [] => ""
  | h :: t => (digit_to_string h) ++ (from_digits_to_string t)
  end.

Definition circular_shift_impl (x : nat) (shift : nat) : string :=
  let digits := to_digits x in
  let len := length digits in
  if (x =? 0)%nat then
    "0"
  else
    if (len <? shift)%nat then
      from_digits_to_string (rev digits)
    else
      let effective_shift := shift mod len in
      if (effective_shift =? 0)%nat then
        from_digits_to_string digits
      else
        let split_point := len - effective_shift in
        let new_head := skipn split_point digits in
        let new_tail := firstn split_point digits in
        from_digits_to_string (new_head ++ new_tail).



Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.
Require Import Recdef.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
Require Import base_conversion_lib.
Require Import string_bridge.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition problem_65_pre (x shift : Z) : Prop :=
  True.

Definition decimal_digits (x : Z) : list Z :=
  map (fun d => 48 + Z.of_nat d) (to_digits (Z.to_nat x)).

Definition circular_shift_index (len shift i : Z) : Z :=
  if Z.ltb len shift then len - 1 - i else (len - shift + i) mod len.

Definition circular_shift_output (x shift : Z) : list Z :=
  let digits := decimal_digits x in
  let len := Zlength digits in
  if Z.ltb len shift then
    rev digits
  else
    sublist (len - shift) len digits ++ sublist 0 (len - shift) digits.

Definition problem_65_spec (x shift : Z) (output : list Z) : Prop :=
  output = circular_shift_output x shift.

Definition circular_shift_prefix
  (x shift i : Z) (out_l : list Z) : Prop :=
  out_l = sublist 0 i (circular_shift_output x shift).

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

Lemma base_digits_pos_length_pos : forall n base,
  0 < n -> 0 < Zlength (base_digits_pos n base).
Proof.
  intros n base Hn.
  unfold base_digits_pos.
  replace (Z.leb n 0) with false by (symmetry; apply Z.leb_gt; lia).
  apply base_digits_length_pos.
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
  base <= 10 ->
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

Lemma base_fill_full_state_step_10 : forall orig x digits out_l,
  0 < x ->
  0 <= digits ->
  base_fill_full_state orig 10 x (digits + 1) out_l ->
  base_fill_full_state orig 10 (x / 10) digits
    (replace_Znth digits (signed_last_nbits (48 + x mod 10) 8) out_l).
Proof.
  intros orig x digits out_l Hx Hdigits Hstate.
  eapply base_fill_full_state_step.
  - exact Hx.
  - lia.
  - lia.
  - exact Hstate.
Qed.

Lemma Zlength_replace_Znth_44 : forall {A : Type} (l : list A) n (v : A),
  Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros.
  apply Zlength_replace_Znth.
Qed.

Lemma Zlength_map_65 : forall {A B} (f : A -> B) (l : list A),
  Zlength (map f l) = Zlength l.
Proof.
  intros.
  repeat rewrite Zlength_correct.
  rewrite length_map.
  reflexivity.
Qed.

Lemma Znth_map_65 : forall {A B} (f : A -> B) l i da db,
  0 <= i < Zlength l ->
  Znth i (map f l) db = f (Znth i l da).
Proof.
  intros A B f l i da db Hi.
  unfold Znth.
  rewrite nth_indep with (d' := f da).
  - rewrite map_nth.
    reflexivity.
  - rewrite length_map.
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
Qed.

Lemma Znth_Zseq_65 : forall start len i,
  0 <= i < Z.of_nat len ->
  Znth i (Zseq start len) 0 = start + i.
Proof.
  intros start len i Hi.
  unfold Znth.
  rewrite Zseq_nth.
  - rewrite Z2Nat.id by lia.
    reflexivity.
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    lia.
Qed.

Lemma to_digits_fuel_enough_65 : forall fuel n,
  (0 < n)%nat ->
  (n <= fuel)%nat ->
  to_digits_fuel n fuel = to_digits n.
Proof.
  assert (Hmain : forall n fuel,
    (0 < n)%nat ->
    (n <= fuel)%nat ->
    to_digits_fuel n fuel = to_digits n).
  { induction n as [n IH] using lt_wf_ind.
    intros fuel Hpos Hle.
    destruct fuel as [|fuel]; [lia|].
    simpl.
    destruct (n <? 10)%nat eqn:Hsmall.
    - unfold to_digits.
      replace (n =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
      destruct n as [|n']; [lia|].
      simpl.
      rewrite Hsmall.
      reflexivity.
    - unfold to_digits.
      replace (n =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
      destruct n as [|n']; [lia|].
      simpl.
      rewrite Hsmall.
      f_equal.
      transitivity (to_digits (S n' / 10)%nat).
      + apply IH.
        * apply Nat.ltb_ge in Hsmall.
          apply Nat.div_lt; lia.
        * apply Nat.ltb_ge in Hsmall.
          apply Nat.div_str_pos; lia.
        * apply Nat.ltb_ge in Hsmall.
          assert ((S n' / 10 < S n')%nat) by (apply Nat.div_lt; lia).
          lia.
      + symmetry.
        apply IH.
        * apply Nat.ltb_ge in Hsmall.
          apply Nat.div_lt; lia.
        * apply Nat.ltb_ge in Hsmall.
          apply Nat.div_str_pos; lia.
        * apply Nat.ltb_ge in Hsmall.
          assert ((S n' / 10 < S n')%nat) by (apply Nat.div_lt; lia).
          lia. }
  intros fuel n Hpos Hle.
  apply Hmain; assumption.
Qed.

Lemma decimal_digits_zero : decimal_digits 0 = [48].
Proof.
  reflexivity.
Qed.

Lemma decimal_digits_step : forall x,
  10 <= x ->
  decimal_digits x =
    decimal_digits (x / 10) ++ [48 + x mod 10].
Proof.
  intros x Hx.
  unfold decimal_digits.
  unfold to_digits at 1.
  replace (Z.to_nat x =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  destruct (Z.to_nat x) as [|xn] eqn:Hxnat; [lia|].
  simpl.
  replace (S xn <? 10)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  rewrite map_app.
  f_equal.
  - rewrite to_digits_fuel_enough_65.
    + replace (Z.to_nat (x / 10)) with (S xn / 10)%nat.
      * reflexivity.
      * rewrite <- Hxnat.
        symmetry.
        apply Z2Nat.inj_div; lia.
    + change (0 < S xn / 10)%nat.
      apply Nat.div_str_pos; lia.
    + change (S xn / 10 <= xn)%nat.
      assert (S xn / 10 < S xn)%nat by (apply Nat.div_lt; lia).
      lia.
  - replace (x mod 10) with (Z.of_nat (Z.to_nat (x mod 10))).
    + rewrite Z2Nat.inj_mod by lia.
      rewrite Hxnat.
      reflexivity.
    + rewrite Z2Nat.id; [reflexivity|].
      pose proof (Z.mod_pos_bound x 10 ltac:(lia)).
      lia.
Qed.

Lemma base_digits_10_decimal_digits : forall x,
  0 <= x ->
  base_digits x 10 = decimal_digits x.
Proof.
  intros x Hx.
  remember 10 as b eqn:Hb.
  change (base_digits x b = decimal_digits x).
  functional induction (base_digits x b); subst.
  - apply Z.leb_le in e. lia.
  - apply Z.leb_le in e0.
    assert (n = 0) by lia. subst n.
    apply decimal_digits_zero.
  - apply Z.leb_gt in e0.
    apply Z.ltb_lt in e1.
    unfold decimal_digits, to_digits.
    replace (Z.to_nat n =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    destruct (Z.to_nat n) as [|xn] eqn:Hxnat; [lia|].
    simpl.
    replace (S xn <? 10)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    change ([48 + n] = [48 + Z.of_nat (S xn)]).
    f_equal. f_equal.
    apply Z2Nat.inj.
    + lia.
    + lia.
    + rewrite Hxnat. rewrite Nat2Z.id. reflexivity.
  - apply Z.leb_gt in e0.
    apply Z.ltb_ge in e1.
    rewrite decimal_digits_step by lia.
    rewrite IHl by (try reflexivity; apply Z.div_pos; lia).
    reflexivity.
Qed.

Lemma decimal_digits_nonzero : forall x k,
  0 <= k < Zlength (decimal_digits x) ->
  Znth k (decimal_digits x) 0 <> 0.
Proof.
  intros x k Hk.
  unfold decimal_digits in *.
  rewrite Zlength_map_65 in Hk.
  rewrite (Znth_map_65 (fun d => 48 + Z.of_nat d)
             (to_digits (Z.to_nat x)) k 0%nat 0) by exact Hk.
  pose proof (Nat2Z.is_nonneg (Znth k (to_digits (Z.to_nat x)) 0%nat)).
  lia.
Qed.

Lemma circular_shift_output_length : forall x shift,
  0 <= shift ->
  Zlength (circular_shift_output x shift) = Zlength (decimal_digits x).
Proof.
  intros x shift Hshift.
  unfold circular_shift_output.
  destruct (Z.ltb (Zlength (decimal_digits x)) shift) eqn:Hcase.
  - repeat rewrite Zlength_correct.
    rewrite length_rev.
    reflexivity.
  - apply Z.ltb_ge in Hcase.
    rewrite Zlength_app.
    destruct (Z_lt_le_dec shift (Zlength (decimal_digits x))).
    + rewrite !Zlength_sublist by lia.
      lia.
    + replace shift with (Zlength (decimal_digits x)) by lia.
      rewrite Zlength_sublist by lia.
      rewrite Zlength_sublist by lia.
      lia.
Qed.

Lemma circular_shift_prefix_length : forall x shift i out_l,
  0 <= shift ->
  0 <= i <= Zlength (circular_shift_output x shift) ->
  circular_shift_prefix x shift i out_l ->
  Zlength out_l = i.
Proof.
  intros x shift i out_l Hshift Hi Hout.
  unfold circular_shift_prefix in Hout.
  subst out_l.
  rewrite Zlength_sublist; lia.
Qed.

Lemma circular_shift_prefix_full : forall x shift out_l,
  0 <= shift ->
  circular_shift_prefix x shift (Zlength (decimal_digits x)) out_l ->
  out_l = circular_shift_output x shift.
Proof.
  intros x shift out_l Hshift Hout.
  unfold circular_shift_prefix in Hout.
  subst out_l.
  rewrite <- (circular_shift_output_length x shift) by lia.
  replace (circular_shift_output x shift) with
    (circular_shift_output x shift ++ nil) at 2 by apply app_nil_r.
  rewrite sublist_app_exact1.
  reflexivity.
Qed.

Lemma circular_shift_prefix_snoc : forall x shift i out_l,
  0 <= shift ->
  0 <= i < Zlength (circular_shift_output x shift) ->
  circular_shift_prefix x shift i out_l ->
  circular_shift_prefix x shift (i + 1)
    (out_l ++ Znth i (circular_shift_output x shift) 0 :: nil).
Proof.
  intros x shift i out_l Hshift Hi Hout.
  unfold circular_shift_prefix in *.
  subst out_l.
  assert (Hlo : 0 <= 0 <= i) by lia.
  assert (Hhi : i <= i + 1 <= Zlength (circular_shift_output x shift)) by lia.
  rewrite (sublist_split 0 (i + 1) i
             (circular_shift_output x shift) Hlo Hhi).
  rewrite (sublist_single 0 i (circular_shift_output x shift)) by lia.
  reflexivity.
Qed.

Lemma Znth_rev_65 : forall {A : Type} (l : list A) (d : A) i,
  0 <= i < Zlength l ->
  Znth i (rev l) d = Znth (Zlength l - 1 - i) l d.
Proof.
  intros A l d i Hi.
  unfold Znth.
  rewrite rev_nth.
  - assert (Hnat :
      Z.to_nat (Zlength l - 1 - i) =
      (List.length l - S (Z.to_nat i))%nat).
    { apply Nat2Z.inj.
      rewrite Z2Nat.id by lia.
      rewrite Nat2Z.inj_sub by (rewrite Zlength_correct in Hi; lia).
      rewrite Nat2Z.inj_succ.
      rewrite Z2Nat.id by lia.
      rewrite Zlength_correct.
      lia. }
    rewrite Hnat.
    reflexivity.
  - rewrite Zlength_correct in Hi.
    lia.
Qed.

Lemma circular_shift_output_reverse_char : forall x shift i,
  0 <= x ->
  Zlength (decimal_digits x) < shift ->
  0 <= i < Zlength (decimal_digits x) ->
  Znth i (circular_shift_output x shift) 0 =
  Znth (Zlength (decimal_digits x) - 1 - i) (decimal_digits x) 0.
Proof.
  intros x shift i Hx Hshift Hi.
  unfold circular_shift_output.
  replace (Z.ltb (Zlength (decimal_digits x)) shift) with true
    by (symmetry; apply Z.ltb_lt; lia).
  apply Znth_rev_65.
  lia.
Qed.

Lemma circular_shift_output_rot_char : forall x shift i,
  0 <= x ->
  0 <= shift <= Zlength (decimal_digits x) ->
  0 <= i < Zlength (decimal_digits x) ->
  Znth i (circular_shift_output x shift) 0 =
  Znth ((Zlength (decimal_digits x) - shift + i) mod
        Zlength (decimal_digits x)) (decimal_digits x) 0.
Proof.
  intros x shift i Hx Hshift Hi.
  unfold circular_shift_output.
  replace (Z.ltb (Zlength (decimal_digits x)) shift) with false
    by (symmetry; apply Z.ltb_ge; lia).
  assert (Hlen_pos : 0 < Zlength (decimal_digits x)) by lia.
  destruct (Z_lt_le_dec i shift) as [Hfirst | Hsecond].
  - rewrite app_Znth1.
    2:{ rewrite Zlength_sublist by lia. lia. }
    rewrite Znth_sublist by lia.
    replace (i + (Zlength (decimal_digits x) - shift))
      with (Zlength (decimal_digits x) - shift + i) by lia.
    rewrite Z.mod_small by lia.
    reflexivity.
  - rewrite app_Znth2.
    2:{ rewrite Zlength_sublist by lia. lia. }
    rewrite Zlength_sublist by lia.
    rewrite Znth_sublist by lia.
    replace (i - (Zlength (decimal_digits x) - (Zlength (decimal_digits x) - shift)))
      with (i - shift) by lia.
    replace (i - shift + 0) with (i - shift) by lia.
    replace ((Zlength (decimal_digits x) - shift + i) mod
             Zlength (decimal_digits x))
      with (i - shift) by (apply Z.mod_unique with (q := 1); lia).
    reflexivity.
Qed.

Lemma circular_shift_output_nonzero : forall x shift k,
  0 <= x ->
  0 <= shift ->
  0 <= k < Zlength (circular_shift_output x shift) ->
  Znth k (circular_shift_output x shift) 0 <> 0.
Proof.
  intros x shift k Hx Hshift Hk.
  pose proof (circular_shift_output_length x shift Hshift) as Hlen.
  destruct (Z.ltb (Zlength (decimal_digits x)) shift) eqn:Hcase.
  - apply Z.ltb_lt in Hcase.
    rewrite (circular_shift_output_reverse_char x shift k) by
      (try lia; rewrite <- circular_shift_output_length by lia; lia).
    apply decimal_digits_nonzero.
    lia.
  - apply Z.ltb_ge in Hcase.
    rewrite (circular_shift_output_rot_char x shift k) by
      (try lia; rewrite <- circular_shift_output_length by lia; lia).
    apply decimal_digits_nonzero.
    pose proof (Z.mod_pos_bound (Zlength (decimal_digits x) - shift + k)
      (Zlength (decimal_digits x)) ltac:(lia)).
    lia.
Qed.

Lemma problem_65_spec_intro : forall x shift,
  0 <= x ->
  0 <= shift ->
  problem_65_spec x shift (circular_shift_output x shift).
Proof.
  intros.
  unfold problem_65_spec.
  reflexivity.
Qed.

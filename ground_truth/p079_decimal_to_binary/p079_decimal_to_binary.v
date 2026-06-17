(* spec/79 *)
(* def decimal_to_binary(decimal):
"""You will be given a number in decimal form and your task is to convert it to
binary format. The function should return a string, with each character representing a binary
number. Each character in the string will be '0' or '1'.

There will be an extra couple of characters 'db' at the beginning and at the end of the string.
The extra characters are there to help with the format.

Examples:
decimal_to_binary(15) # returns "db1111db"
decimal_to_binary(32) # returns "db100000db"
""" *)
(* 导入Coq中处理字符串和列表所需的基础库 *)
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope string_scope.

(*
 * @brief 将布尔值列表转换为由 '0' 和 '1' 组成的字符串。
 *
 * 例如: binary_list_to_string [true; true; false; true] 会返回 "1101"
 *)
Fixpoint nat_to_binary_string_aux (n fuel : nat) : string :=
  match fuel with
  | O => ""
  | S fuel' =>
      match n with
      | O => "0"
      | 1 => "1"
      | _ =>
          if Nat.even n then
            nat_to_binary_string_aux (n / 2) fuel' ++ "0"
          else
            nat_to_binary_string_aux ((n - 1) / 2) fuel' ++ "1"
      end
  end.

Definition nat_to_binary_string (n : nat) : string :=
  match n with
  | O => "0"
  | _ => nat_to_binary_string_aux n n
  end.

Definition decimal_to_binary_impl (decimal : nat) : string :=
  "db" ++ nat_to_binary_string decimal ++ "db".


(* spec/103 *)
(* You are given two positive integers n and m, and your task is to compute the
average of the integers from n through m (including n and m).
Round the answer to the nearest integer and convert that to binary.
If n is greater than m, return -1.
Example:
rounded_avg(1, 5) => "11"
rounded_avg(7, 5) => "-1"
rounded_avg(10, 20) => "1111"
rounded_avg(20, 33) => "11010" *)

(* 引入所需的库 *)
Require Import ZArith.
Require Import String.
Require Import PArith. (* 用于 positive 类型 *)
Open Scope Z_scope.

(*
  一个作用于 positive 类型的递归辅助函数，用于生成二进制字符串。
  这是在 Coq 中进行此类转换的标准方法。
*)
Fixpoint to_binary_p (p : positive) : string :=
  match p with
  | xH    => "1" (* Base case for p = 1 *)
  | xO p' => to_binary_p p' ++ "0" (* Case for p = 2 * p' *)
  | xI p' => to_binary_p p' ++ "1" (* Case for p = 2 * p' + 1 *)
  end.

(*
  主转换函数，用于将 Z 类型（整数）转换为不带前缀的二进制字符串。
  它处理了 0 的情况，并使用 to_binary_p 处理正数。
*)
Definition to_binary (n : Z) : string :=
  match n with
  | Z0 => "0"
  | Zpos p => to_binary_p p
  | Zneg _ => "-1"
  end.

Definition rounded_avg_impl (n m : Z) : string :=
  if Z.gtb n m then
    "-1"
  else
    to_binary ((n + m) / 2).

(* n 与 m 为正整数 *)
Definition problem_103_pre (n m : Z) : Prop := n > 0 /\ m > 0.

Definition problem_103_spec (n m : Z) (output : string) : Prop :=
  output = rounded_avg_impl n m.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
Require Export string_bridge.
Require Export base_conversion_lib binary_digits_lib.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition problem_79_pre (decimal : Z) : Prop :=
  True.

Definition decorated_binary_digits (decimal : Z) : list Z :=
  [100; 98] ++ binary_digits decimal ++ [100; 98].

Definition problem_79_spec (decimal : Z) (output : list Z) : Prop :=
  output = decorated_binary_digits decimal.

Definition decimal_binary_full_state
  (orig x digits : Z) (out_l : list Z) : Prop :=
  exists payload,
    binary_fill_full_state orig x digits payload /\
    out_l = [100; 98] ++ payload ++ [100; 98].

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

Lemma decorated_binary_digits_zero :
  decorated_binary_digits 0 = [100; 98; 48; 100; 98].
Proof.
  unfold decorated_binary_digits, binary_digits.
  rewrite base_digits_equation.
  replace (2 <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
  replace (0 <=? 0) with true by (symmetry; apply Z.leb_le; lia).
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
        replace (2 <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
        replace (0 <=? 0) with true by (symmetry; apply Z.leb_le; lia).
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

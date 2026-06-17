(* spec/44 *)
(* Change numerical base of input number x to base.
return string representation after the conversion.
base numbers are less than 10.
>>> change_base(8, 3)
'22'
>>> change_base(8, 2)
'1000'
>>> change_base(7, 2)
'111' *)

(* Spec(x : int, base : int, output : string) :=

​	∀i ∈ [0, length(output)), output[i] < base /\
​	$∑_{i=0}^{length(output)-1}$ ToNum(output[i]) * base^(length(output) - i - 1) = x *)

(* 引入所需的Coq库 *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.

Import ListNotations.

(*
  辅助函数，用于将一个数字字符（如 '0', '1', ...）
  转换为其对应的自然数（如 0, 1, ...）。
*)
Definition nat_of_digit (c : ascii) : nat :=
  Ascii.nat_of_ascii c - Ascii.nat_of_ascii "0"%char.

(*
  程序规约 Spec 的定义。
  - x:      输入的非负整数。
  - base:   转换的目标基数 (>= 2)。
  - output: 转换后得到的字符串。
*)
(* Pre: base must be at least 2 for a valid base conversion *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Wf_Z.
Require Import Coq.micromega.Lia.
Require Import Recdef.
From compcert.lib Require Import Coqlib.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
Require Import string_bridge.

Local Open Scope Z_scope.

Definition SingleSome {A : Type} (l : list (option A)) (n : Z) (a : A) : Prop :=
  Znth n l None = Some a /\
  forall m, 0 <= m < Zlength l -> m <> n -> Znth m l None = None.

Definition repeat_Z {A: Type} (a: A) (n: Z): list A :=
  repeat a (Z.to_nat n).

Function base_digits (n base : Z) {measure Z.to_nat n} : list Z :=
  if Z.leb base 1 then [48]
  else if Z.leb n 0 then [48]
  else if Z.ltb n base then [48 + n]
  else base_digits (n / base) base ++ [48 + (n mod base)].
Proof.
  intros n base Hbase Hnpos Hnotlt.
  apply Z.leb_gt in Hbase.
  apply Z.leb_gt in Hnpos.
  apply Z.ltb_ge in Hnotlt.
  apply Z2Nat.inj_lt.
  - apply Z.div_pos; lia.
  - lia.
  - apply Z.div_lt; lia.
Defined.

Definition base_digits_pos (n base : Z) : list Z :=
  if Z.leb n 0 then [] else base_digits n base.

Definition problem_44_pre (x base : Z) : Prop :=
  0 <= x /\ 2 <= base < 10.

Definition problem_44_spec (x base : Z) (output : list Z) : Prop :=
  Forall (fun c => 48 <= c < 48 + base) output /\
  fold_left (fun acc c => acc * base + (c - 48)) output 0 = x.

Definition digit_value (c : Z) : Z := c - 48.

Fixpoint digits_value (base : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | c :: rest => digits_value base rest + digit_value c * Z.pow base (Zlength rest)
  end.

Definition base_count_state (orig base t digits : Z) : Prop :=
  0 <= t /\
  0 <= digits /\
  digits + Zlength (base_digits_pos t base) =
    Zlength (base_digits_pos orig base).

Definition base_fill_state
  (orig base x digits : Z) (suffix : list Z) : Prop :=
  0 <= x /\
  0 <= digits /\
  digits = Zlength (base_digits_pos x base) /\
  base_digits orig base = base_digits_pos x base ++ suffix.

Definition base_fill_full_state
  (orig base x digits : Z) (out_l : list Z) : Prop :=
  exists suffix,
    base_fill_state orig base x digits suffix /\
    out_l = repeat_Z 0 digits ++ suffix.

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

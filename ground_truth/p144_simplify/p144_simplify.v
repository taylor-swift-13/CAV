(* spec/144 *)
(* def simplify(x, n):
Your task is to implement a function that will simplify the expression
x * n. The function returns True if x * n evaluates to a whole number and False
otherwise. Both x and n, are string representation of a fraction, and have the following format,
<numerator>/<denominator> where both numerator and denominator are positive whole numbers.

You can assume that x, and n are valid fractions, and do not have zero as denominator.

simplify("1/5", "5/1") = True
simplify("1/6", "2/1") = False
simplify("7/10", "10/2") = False *)
(* 导入所需的Coq库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* 将单个ASCII字符转换为数字 (0-9)，假设输入合法 *)
Definition char_to_digit (c : ascii) : nat :=
  let n := nat_of_ascii c in
  let zero := nat_of_ascii ("0"%char) in
  n - zero.

(* 辅助函数：将list ascii转换为自然数 *)
Fixpoint list_ascii_to_nat_aux (l : list ascii) (acc : nat) : nat :=
  match l with
  | [] => acc
  | c :: l' => list_ascii_to_nat_aux l' (acc * 10 + char_to_digit c)
  end.

(* 主函数：将list ascii转换为自然数 *)
Definition list_ascii_to_nat (l : list ascii) : nat :=
  list_ascii_to_nat_aux l 0.

Definition is_digit_ascii (c : ascii) : Prop :=
  nat_of_ascii ("0"%char) <= nat_of_ascii c <= nat_of_ascii ("9"%char).

Definition all_digits (l : list ascii) : Prop :=
  Forall is_digit_ascii l.

(*
 * 规约：Parse_Fraction
 * 描述：将一个由ASCII字符组成的列表解析为一个由分子和分母组成的自然数对。
 *
 * 参数：
 *   s: 代表分数字符串的 list ascii。
 *   num: 解析出的分子（自然数）。
 *   den: 解析出的分母（自然数）。
 *)
Definition Parse_Fraction (s : list ascii) (num den : nat) : Prop :=
  exists num_s den_s : list ascii,
    s = num_s ++ ["/"%char] ++ den_s /\
    num = list_ascii_to_nat num_s /\
    den = list_ascii_to_nat den_s.

(*
 * 规约：simplify_spec
 * 描述：这是`simplify`函数的顶层规约。它规定了输入与期望的布尔输出之间的关系。
 *       此版本完全使用 list ascii。
 *
 * 参数：
 *   x: 代表第一个分数的 list ascii。
 *   n: 代表第二个分数的 list ascii。
 *   output: 函数的期望布尔输出。
 *)
 (* 约束：x 与 n 均为有效分数串，且分子/分母为正整数 *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Export string_bridge.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition digit_char (c : Z) : Prop :=
  48 <= c <= 57.

Definition digit_value (c : Z) : Z :=
  c - 48.

Fixpoint parse_digits_z_aux (l : list Z) (acc : Z) : Z :=
  match l with
  | [] => acc
  | c :: rest => parse_digits_z_aux rest (acc * 10 + digit_value c)
  end.

Definition parse_digits (l : list Z) : Z :=
  parse_digits_z_aux l 0.

Definition fraction_parts (s : list Z) (slash num den : Z) : Prop :=
  0 < slash < Zlength s /\
  Znth slash s 0 = 47 /\
  (forall k, 0 <= k < slash -> digit_char (Znth k s 0)) /\
  (forall k, slash < k < Zlength s -> digit_char (Znth k s 0)) /\
  num = parse_digits (sublist 0 slash s) /\
  den = parse_digits (sublist (slash + 1) (Zlength s) s) /\
  (forall i, 0 <= i <= slash ->
     0 <= parse_digits (sublist 0 i s) <= num) /\
  (forall i, slash + 1 <= i <= Zlength s ->
     0 <= parse_digits (sublist (slash + 1) i s) <= den) /\
  0 < num /\ 0 < den.

Definition fraction_values_safe (a b c d : Z) : Prop :=
  1 <= a <= 46340 /\
  1 <= b <= 46340 /\
  1 <= c <= 46340 /\
  1 <= d <= 46340.

Definition problem_144_pre (x n : list Z) : Prop :=
  exists sx sn ax bx cn dn,
    fraction_parts x sx ax bx /\
    fraction_parts n sn cn dn.

Definition problem_144_spec (x n : list Z) (output : Z) : Prop :=
  exists sx sn ax bx cn dn,
    fraction_parts x sx ax bx /\
    fraction_parts n sn cn dn /\
    bool_of output = Z.eqb (Z.rem (ax * cn) (bx * dn)) 0.

Lemma parse_digits_aux_app_single : forall l c acc,
  parse_digits_z_aux (l ++ [c]) acc =
  parse_digits_z_aux l acc * 10 + digit_value c.
Proof.
  induction l as [| x xs IH]; intros c acc; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma parse_digits_snoc : forall l c,
  parse_digits (l ++ [c]) =
  parse_digits l * 10 + digit_value c.
Proof.
  intros l c.
  unfold parse_digits.
  apply parse_digits_aux_app_single.
Qed.

Lemma parse_digits_empty : forall l i,
  parse_digits (sublist i i l) = 0.
Proof.
  intros.
  rewrite Zsublist_nil by lia.
  reflexivity.
Qed.

Lemma Znth_app_left : forall (l1 l2 : list Z) i d,
  0 <= i < Zlength l1 ->
  Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros l1 l2 i d Hi.
  unfold Znth.
  rewrite app_nth1.
  - reflexivity.
  - rewrite Zlength_correct in Hi.
    assert ((Z.to_nat i < Datatypes.length l1)%nat).
    { apply Nat2Z.inj_lt.
      rewrite Z2Nat.id by lia.
      lia. }
    lia.
Qed.

Lemma parse_digits_step_sublist : forall l lo i,
  0 <= lo <= i ->
  i < Zlength l ->
  parse_digits (sublist lo (i + 1) l) =
    parse_digits (sublist lo i l) * 10 + digit_value (Znth i l 0).
Proof.
  intros l lo i Hlo Hi.
  rewrite (sublist_split lo (i + 1) i l) by lia.
  rewrite (sublist_single 0 i l) by lia.
  apply parse_digits_snoc.
Qed.

Lemma fraction_parts_num_digit : forall s slash num den i,
  fraction_parts s slash num den ->
  0 <= i < slash ->
  digit_char (Znth i s 0).
Proof.
  intros s slash num den i Hparts Hi.
  unfold fraction_parts in Hparts.
  destruct Hparts as (_ & _ & Hdigits & _).
  apply Hdigits; lia.
Qed.

Lemma fraction_parts_slash_char : forall s slash num den,
  fraction_parts s slash num den ->
  Znth slash s 0 = 47.
Proof.
  intros s slash num den Hparts.
  unfold fraction_parts in Hparts.
  tauto.
Qed.

Lemma fraction_parts_den_digit : forall s slash num den i,
  fraction_parts s slash num den ->
  slash < i < Zlength s ->
  digit_char (Znth i s 0).
Proof.
  intros s slash num den i Hparts Hi.
  unfold fraction_parts in Hparts.
  destruct Hparts as (_ & _ & _ & Hdigits & _).
  apply Hdigits; lia.
Qed.

Lemma fraction_parts_num_value : forall s slash num den,
  fraction_parts s slash num den ->
  num = parse_digits (sublist 0 slash s).
Proof.
  intros s slash num den Hparts.
  unfold fraction_parts in Hparts.
  tauto.
Qed.

Lemma fraction_parts_den_value : forall s slash num den,
  fraction_parts s slash num den ->
  den = parse_digits (sublist (slash + 1) (Zlength s) s).
Proof.
  intros s slash num den Hparts.
  unfold fraction_parts in Hparts.
  tauto.
Qed.

Lemma fraction_parts_prefix_num_bound : forall s slash num den i,
  fraction_parts s slash num den ->
  0 <= i <= slash ->
  0 <= parse_digits (sublist 0 i s) <= num.
Proof.
  intros s slash num den i Hparts Hi.
  unfold fraction_parts in Hparts.
  destruct Hparts as (_ & _ & _ & _ & _ & _ & Hprefix & _).
  apply Hprefix; lia.
Qed.

Lemma fraction_parts_prefix_den_bound : forall s slash num den i,
  fraction_parts s slash num den ->
  slash + 1 <= i <= Zlength s ->
  0 <= parse_digits (sublist (slash + 1) i s) <= den.
Proof.
  intros s slash num den i Hparts Hi.
  unfold fraction_parts in Hparts.
  destruct Hparts as (_ & _ & _ & _ & _ & _ & _ & Hprefix & _).
  apply Hprefix; lia.
Qed.

Lemma fraction_parts_slash_char_app : forall s slash num den,
  fraction_parts s slash num den ->
  Znth slash (s ++ [0]) 0 = 47.
Proof.
  intros s slash num den Hparts.
  rewrite Znth_app_left by (unfold fraction_parts in Hparts; lia).
  apply fraction_parts_slash_char with (num := num) (den := den).
  exact Hparts.
Qed.

Lemma fraction_parts_num_loop_lt : forall s slash num den i,
  fraction_parts s slash num den ->
  0 <= i <= slash ->
  Znth i (s ++ [0]) 0 <> 47 ->
  i < slash.
Proof.
  intros s slash num den i Hparts Hi Hneq.
  destruct (Z_lt_ge_dec i slash) as [Hlt | Hge]; [exact Hlt |].
  assert (i = slash) by lia.
  subst.
  exfalso.
  apply Hneq.
  apply fraction_parts_slash_char_app with (num := num) (den := den).
  exact Hparts.
Qed.

Lemma fraction_parts_num_digit_app : forall s slash num den i,
  fraction_parts s slash num den ->
  0 <= i < slash ->
  digit_char (Znth i (s ++ [0]) 0).
Proof.
  intros s slash num den i Hparts Hi.
  rewrite Znth_app_left by (unfold fraction_parts in Hparts; lia).
  exact (fraction_parts_num_digit s slash num den i Hparts Hi).
Qed.

Lemma fraction_parts_den_digit_app : forall s slash num den i,
  fraction_parts s slash num den ->
  slash < i < Zlength s ->
  digit_char (Znth i (s ++ [0]) 0).
Proof.
  intros s slash num den i Hparts Hi.
  rewrite Znth_app_left by (unfold fraction_parts in Hparts; lia).
  exact (fraction_parts_den_digit s slash num den i Hparts Hi).
Qed.

Lemma fraction_parts_num_step_bound : forall s slash num den i,
  fraction_parts s slash num den ->
  0 <= i < slash ->
  0 <= parse_digits (sublist 0 (i + 1) s) <= num.
Proof.
  intros s slash num den i Hparts Hi.
  exact (fraction_parts_prefix_num_bound s slash num den (i + 1) Hparts ltac:(lia)).
Qed.

Lemma fraction_parts_den_step_bound : forall s slash num den i,
  fraction_parts s slash num den ->
  slash + 1 <= i < Zlength s ->
  0 <= parse_digits (sublist (slash + 1) (i + 1) s) <= den.
Proof.
  intros s slash num den i Hparts Hi.
  exact (fraction_parts_prefix_den_bound s slash num den (i + 1) Hparts ltac:(lia)).
Qed.

Lemma fraction_parts_den_done : forall s slash num den i d,
  fraction_parts s slash num den ->
  i >= Zlength s ->
  i <= Zlength s ->
  d = parse_digits (sublist (slash + 1) i s) ->
  d = den.
Proof.
  intros s slash num den i d Hparts Hge Hle Hd.
  assert (i = Zlength s) by lia.
  subst i.
  rewrite Hd.
  symmetry.
  apply fraction_parts_den_value with (slash := slash) (num := num).
  exact Hparts.
Qed.

Lemma fraction_parts_num_step_value : forall s slash num den i,
  fraction_parts s slash num den ->
  0 <= i < slash ->
  parse_digits (sublist 0 (i + 1) s) =
    parse_digits (sublist 0 i s) * 10 + (Znth i (s ++ [0]) 0 - 48).
Proof.
  intros s slash num den i Hparts Hi.
  rewrite Znth_app_left by (unfold fraction_parts in Hparts; lia).
  unfold digit_value.
  rewrite parse_digits_step_sublist by (unfold fraction_parts in Hparts; lia).
  reflexivity.
Qed.

Lemma fraction_parts_den_step_value : forall s slash num den i,
  fraction_parts s slash num den ->
  slash + 1 <= i < Zlength s ->
  parse_digits (sublist (slash + 1) (i + 1) s) =
    parse_digits (sublist (slash + 1) i s) * 10 + (Znth i (s ++ [0]) 0 - 48).
Proof.
  intros s slash num den i Hparts Hi.
  rewrite Znth_app_left by (unfold fraction_parts in Hparts; lia).
  unfold digit_value.
  rewrite parse_digits_step_sublist by (unfold fraction_parts in Hparts; lia).
  reflexivity.
Qed.

Lemma fraction_parts_slash_index : forall s slash num den i,
  fraction_parts s slash num den ->
  0 <= i <= slash ->
  Znth i (s ++ [0]) 0 = 47 ->
  i = slash.
Proof.
  intros s slash num den i Hparts Hi Hchar.
  destruct (Z_lt_ge_dec i slash) as [Hlt | Hge]; [| lia].
  rewrite Znth_app_left in Hchar by (unfold fraction_parts in Hparts; lia).
  pose proof (fraction_parts_num_digit s slash num den i Hparts ltac:(lia)) as Hdigit.
  unfold digit_char in Hdigit.
  lia.
Qed.

Lemma problem_144_spec_intro : forall x n sx sn a b c d output,
  fraction_parts x sx a b ->
  fraction_parts n sn c d ->
  fraction_values_safe a b c d ->
  output = (if Z.eqb (Z.rem (a * c) (b * d)) 0 then 1 else 0) ->
  problem_144_spec x n output.
Proof.
  intros x n sx sn a b c d output Hx Hn _ Hout.
  subst output.
  unfold problem_144_spec.
  exists sx, sn, a, b, c, d.
  split; [exact Hx |].
  split; [exact Hn |].
  unfold bool_of.
  destruct (Z.eqb (Z.rem (a * c) (b * d)) 0); reflexivity.
Qed.

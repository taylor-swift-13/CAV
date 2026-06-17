(* spec/156 *)
(* def int_to_mini_roman(number):
"""
Given a positive integer, obtain its roman numeral equivalent as a string,
and return it in lowercase.
Restrictions: 1 <= num <= 1000

Examples:
>>> int_to_mini_roman(19) == 'xix'
>>> int_to_mini_roman(152) == 'clii'
>>> int_to_mini_roman(426) == 'cdxxvi'
""" *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith. (* <-- 添加这一行来导入算术库 *)
Import ListNotations.

(*
  一个辅助规约，用于定义单个数字（0-9）到其小写罗马数字字符（作为 list ascii）的映射。
  - roman_char:  i, v, x
*)
Definition roman_digit_spec (one ten five : ascii) (digit : nat) (res : list ascii) : Prop :=
  (digit = 0 /\ res = []) \/
  (digit = 1 /\ res = [one]) \/
  (digit = 2 /\ res = [one; one]) \/
  (digit = 3 /\ res = [one; one; one]) \/
  (digit = 4 /\ res = [one; five]) \/
  (digit = 5 /\ res = [five]) \/
  (digit = 6 /\ res = [five; one]) \/
  (digit = 7 /\ res = [five; one; one]) \/
  (digit = 8 /\ res = [five; one; one; one]) \/
  (digit = 9 /\ res = [one; ten]).

(* 输入限制：1 <= number <= 1000 *)

(*
  int_to_mini_roman 程序的程序规约
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
Require Import string_bridge.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition problem_156_pre (number : Z) : Prop :=
  1 <= number <= 1000.

Definition roman_digit_list (one ten five digit : Z) : list Z :=
  match digit with
  | 0 => []
  | 1 => [one]
  | 2 => [one; one]
  | 3 => [one; one; one]
  | 4 => [one; five]
  | 5 => [five]
  | 6 => [five; one]
  | 7 => [five; one; one]
  | 8 => [five; one; one; one]
  | 9 => [one; ten]
  | _ => []
  end.

Definition roman_digit
  (one ten five digit : Z) (chunk : list Z) : Prop :=
  chunk = roman_digit_list one ten five digit.

Definition roman_thousand_list (number : Z) : list Z :=
  if Z.eqb number 1000 then [109] else [].

Definition roman_thousand (number : Z) (out_l : list Z) : Prop :=
  out_l = roman_thousand_list number.

Definition roman_prefix1_list (number : Z) : list Z :=
  roman_thousand_list number ++
  roman_digit_list 99 109 100 ((number / 100) mod 10).

Definition roman_prefix1 (number : Z) (out_l : list Z) : Prop :=
  out_l = roman_prefix1_list number.

Definition roman_prefix2_list (number : Z) : list Z :=
  roman_prefix1_list number ++
  roman_digit_list 120 99 108 ((number / 10) mod 10).

Definition roman_prefix2 (number : Z) (out_l : list Z) : Prop :=
  out_l = roman_prefix2_list number.

Definition roman_output_list (number : Z) : list Z :=
  roman_prefix2_list number ++
  roman_digit_list 105 120 118 (number mod 10).

Definition roman_output (number : Z) (out_l : list Z) : Prop :=
  out_l = roman_output_list number.

Definition problem_156_spec (number : Z) (output : list Z) : Prop :=
  1 <= number <= 1000 /\
  output = roman_output_list number.

(* Helper lemmas migrated from the old proof, with names aligned to the input spec. *)
Lemma roman_digit_length_bound : forall one ten five digit chunk,
  0 <= digit <= 9 ->
  roman_digit one ten five digit chunk ->
  0 <= Zlength chunk <= 4.
Proof.
  intros one ten five digit chunk Hdig Hchunk.
  unfold roman_digit, roman_digit_list in Hchunk.
  subst chunk.
  assert ((Z.to_nat digit <= 9)%nat) by lia.
  rewrite <- (Z2Nat.id digit) by lia.
  destruct (Z.to_nat digit) as
    [|[|[|[|[|[|[|[|[|[|d]]]]]]]]]]; cbn; lia.
Qed.

Lemma roman_output_length_bound : forall number out_l,
  1 <= number <= 1000 ->
  roman_output number out_l ->
  0 <= Zlength out_l < 64.
Proof.
  intros number out_l Hnum Hout.
  unfold roman_output, roman_output_list, roman_prefix2_list,
    roman_prefix1_list, roman_thousand_list in Hout.
  subst out_l.
  repeat rewrite Zlength_app.
  pose proof (roman_digit_length_bound 99 109 100
    ((number / 100) mod 10)
    (roman_digit_list 99 109 100 ((number / 100) mod 10))
    ltac:(pose proof (Z.mod_pos_bound (number / 100) 10 ltac:(lia)); lia)
    ltac:(reflexivity)).
  pose proof (roman_digit_length_bound 120 99 108
    ((number / 10) mod 10)
    (roman_digit_list 120 99 108 ((number / 10) mod 10))
    ltac:(pose proof (Z.mod_pos_bound (number / 10) 10 ltac:(lia)); lia)
    ltac:(reflexivity)).
  pose proof (roman_digit_length_bound 105 120 118
    (number mod 10)
    (roman_digit_list 105 120 118 (number mod 10))
    ltac:(pose proof (Z.mod_pos_bound number 10 ltac:(lia)); lia)
    ltac:(reflexivity)).
  assert (0 <= Zlength (if Z.eqb number 1000 then [109] else []) <= 1).
  { destruct (Z.eqb number 1000); cbn; lia. }
  lia.
Qed.

Lemma roman_thousand_length_bound : forall number out_l,
  1 <= number <= 1000 ->
  roman_thousand number out_l ->
  0 <= Zlength out_l <= 1.
Proof.
  intros number out_l _ Hout.
  unfold roman_thousand, roman_thousand_list in Hout.
  subst out_l.
  destruct (Z.eqb number 1000); cbn; lia.
Qed.

Lemma roman_prefix1_length_bound : forall number out_l,
  1 <= number <= 1000 ->
  roman_prefix1 number out_l ->
  0 <= Zlength out_l <= 5.
Proof.
  intros number out_l Hnum Hout.
  unfold roman_prefix1, roman_prefix1_list in Hout.
  subst out_l.
  rewrite Zlength_app.
  pose proof (roman_thousand_length_bound number
    (roman_thousand_list number) Hnum ltac:(reflexivity)).
  pose proof (roman_digit_length_bound 99 109 100
    ((number / 100) mod 10)
    (roman_digit_list 99 109 100 ((number / 100) mod 10))
    ltac:(pose proof (Z.mod_pos_bound (number / 100) 10 ltac:(lia)); lia)
    ltac:(reflexivity)).
  lia.
Qed.

Lemma roman_prefix2_length_bound : forall number out_l,
  1 <= number <= 1000 ->
  roman_prefix2 number out_l ->
  0 <= Zlength out_l <= 9.
Proof.
  intros number out_l Hnum Hout.
  unfold roman_prefix2, roman_prefix2_list in Hout.
  subst out_l.
  rewrite Zlength_app.
  pose proof (roman_prefix1_length_bound number
    (roman_prefix1_list number) Hnum ltac:(reflexivity)).
  pose proof (roman_digit_length_bound 120 99 108
    ((number / 10) mod 10)
    (roman_digit_list 120 99 108 ((number / 10) mod 10))
    ltac:(pose proof (Z.mod_pos_bound (number / 10) 10 ltac:(lia)); lia)
    ltac:(reflexivity)).
  lia.
Qed.

Lemma roman_prefix1_step : forall number chunk,
  0 <= number ->
  roman_digit 99 109 100 ((number / 100) mod 10) chunk ->
  roman_prefix1_list number = roman_thousand_list number ++ chunk.
Proof.
  intros number chunk Hnum Hchunk.
  unfold roman_digit in Hchunk.
  unfold roman_prefix1_list.
  subst chunk; reflexivity.
Qed.

Lemma roman_prefix2_step : forall number chunk,
  0 <= number ->
  roman_digit 120 99 108 ((number / 10) mod 10) chunk ->
  roman_prefix2_list number = roman_prefix1_list number ++ chunk.
Proof.
  intros number chunk Hnum Hchunk.
  unfold roman_digit in Hchunk.
  unfold roman_prefix2_list.
  subst chunk; reflexivity.
Qed.

Lemma roman_output_step : forall number chunk,
  roman_digit 105 120 118 (number mod 10) chunk ->
  roman_output_list number = roman_prefix2_list number ++ chunk.
Proof.
  intros number chunk Hchunk.
  unfold roman_digit in Hchunk.
  unfold roman_output_list.
  subst chunk; reflexivity.
Qed.

Lemma p156_Forall_Znth_nonzero : forall l k,
  Forall (fun x => x <> 0) l ->
  0 <= k < Zlength l ->
  Znth k l 0 <> 0.
Proof.
  intros l k Hforall Hk.
  unfold Znth.
  apply Forall_forall with (x := nth (Z.to_nat k) l 0) in Hforall.
  - exact Hforall.
  - apply nth_In.
    rewrite Zlength_correct in Hk.
    lia.
Qed.

Lemma roman_digit_list_nonzero_forall : forall one ten five digit,
  one <> 0 ->
  ten <> 0 ->
  five <> 0 ->
  0 <= digit <= 9 ->
  Forall (fun x => x <> 0) (roman_digit_list one ten five digit).
Proof.
  intros one ten five digit Hone Hten Hfive Hdigit.
  unfold roman_digit_list.
  assert (Hnat_bound : (Z.to_nat digit <= 9)%nat) by lia.
  rewrite <- (Z2Nat.id digit) by lia.
  destruct (Z.to_nat digit) as
    [|[|[|[|[|[|[|[|[|[|d]]]]]]]]]]; cbn.
  - apply Forall_nil.
  - repeat constructor; auto.
  - repeat constructor; auto.
  - repeat constructor; auto.
  - repeat constructor; auto.
  - repeat constructor; auto.
  - repeat constructor; auto.
  - repeat constructor; auto.
  - repeat constructor; auto.
  - repeat constructor; auto.
  - lia.
Qed.

Lemma roman_thousand_list_nonzero_forall : forall number,
  Forall (fun x => x <> 0) (roman_thousand_list number).
Proof.
  intro number.
  unfold roman_thousand_list.
  destruct (Z.eqb number 1000); repeat constructor; lia.
Qed.

Lemma roman_prefix1_list_nonzero_forall : forall number,
  1 <= number <= 1000 ->
  Forall (fun x => x <> 0) (roman_prefix1_list number).
Proof.
  intros number Hnum.
  unfold roman_prefix1_list.
  apply Forall_app.
  split.
  - apply roman_thousand_list_nonzero_forall.
  - apply roman_digit_list_nonzero_forall; try lia.
    pose proof (Z.mod_pos_bound (number / 100) 10 ltac:(lia)).
    lia.
Qed.

Lemma roman_prefix2_list_nonzero_forall : forall number,
  1 <= number <= 1000 ->
  Forall (fun x => x <> 0) (roman_prefix2_list number).
Proof.
  intros number Hnum.
  unfold roman_prefix2_list.
  apply Forall_app.
  split.
  - apply roman_prefix1_list_nonzero_forall; lia.
  - apply roman_digit_list_nonzero_forall; try lia.
    pose proof (Z.mod_pos_bound (number / 10) 10 ltac:(lia)).
    lia.
Qed.

Lemma roman_output_list_nonzero_forall : forall number,
  1 <= number <= 1000 ->
  Forall (fun x => x <> 0) (roman_output_list number).
Proof.
  intros number Hnum.
  unfold roman_output_list.
  apply Forall_app.
  split.
  - apply roman_prefix2_list_nonzero_forall; lia.
  - apply roman_digit_list_nonzero_forall; try lia.
    pose proof (Z.mod_pos_bound number 10 ltac:(lia)).
    lia.
Qed.

Lemma roman_output_list_Znth_nonzero : forall number k,
  1 <= number <= 1000 ->
  0 <= k < Zlength (roman_output_list number) ->
  Znth k (roman_output_list number) 0 <> 0.
Proof.
  intros number k Hnum Hk.
  apply p156_Forall_Znth_nonzero.
  - apply roman_output_list_nonzero_forall; lia.
  - exact Hk.
Qed.


Lemma problem_156_spec_intro : forall number out_l,
  1 <= number <= 1000 ->
  roman_output number out_l ->
  problem_156_spec number out_l.
Proof.
  intros number out_l Hnum Hout.
  unfold problem_156_spec, roman_output in *.
  split; [lia | assumption].
Qed.

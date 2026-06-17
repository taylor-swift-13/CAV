(* spec/163 *)
(* def generate_integers(a, b):
"""
Given two positive integers a and b, return the even digits between a
and b, in ascending order.

For example:
generate_integers(2, 8) => [2, 4, 6, 8]
generate_integers(8, 2) => [2, 4, 6, 8]
generate_integers(10, 14) => []
""" *)
(* 引入所需的基础库 *)
Require Import Coq.Lists.List.      (* List 定义与操作 *)
Require Import Coq.Arith.Arith.      (* 算术相关，包含 min, max, le, lt 等 *)
Require Import Coq.Sorting.Sorted.  (* Sorted 定义 *)
Require Import Coq.Lists.SetoidList.  (* NoDup 定义 *)
Import ListNotations.

(*
  generate_integers_spec 是函数 generate_integers 的程序规约。

  - a, b: 输入的两个自然数。
  - l: 输出的结果列表。

  该规约使用一阶逻辑精确地描述了输入 a, b 与输出列表 l 之间应满足的关系。
*)
(* 输入为正整数 *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition digit_candidates : list Z := [2; 4; 6; 8].

Definition generate_prefix_list (lo i : Z) : list Z :=
  filter (fun d => andb (lo <=? d) (d <? i)) digit_candidates.

Definition generate_list (lo hi : Z) : list Z :=
  generate_prefix_list lo (hi + 1).

Definition generate_bounds (a0 b0 a b : Z) : Prop :=
  a = Z.min a0 b0 /\ b = Z.max a0 b0.

Definition z_min (a b : Z) : Z := Z.min a b.

Definition z_max (a b : Z) : Z := Z.max a b.

Definition generate_prefix (lo i hi : Z) (output : list Z) : Prop :=
  lo <= i <= hi + 1 /\
  output = generate_prefix_list lo i.

Definition problem_163_pre (a b : Z) : Prop :=
  a > 0 /\ b > 0.

Definition problem_163_spec (a b : Z) (output : list Z) : Prop :=
  (forall d : Z,
    In d output <->
      Z.min a b <= d <= Z.max a b /\ d < 10 /\ d mod 2 = 0) /\
  Sorted Z.le output /\
  NoDup output.

(* Helper lemmas migrated from the old proof, with names aligned to the input spec. *)
Lemma generate_prefix_length_le_4 : forall lo i hi output,
  generate_prefix lo i hi output ->
  Zlength output <= 4.
Proof.
  intros lo i hi output [_ Hout].
  rewrite Hout.
  unfold generate_prefix_list, digit_candidates.
  simpl.
  repeat match goal with
  | |- context [if ?b then _ else _] => destruct b
  end;
  simpl;
  repeat (rewrite Zlength_cons || rewrite Zlength_nil);
  lia.
Qed.

Lemma generate_prefix_list_in_163 : forall lo hi z,
  In z (generate_list lo hi) <->
  In z digit_candidates /\ lo <= z <= hi.
Proof.
  intros lo hi z.
  unfold generate_list, generate_prefix_list, digit_candidates.
  repeat rewrite filter_In.
  simpl.
  split.
  - intros [Hin Hfilter].
    apply andb_prop in Hfilter as [Hlo Hhi].
    apply Z.leb_le in Hlo.
    apply Z.ltb_lt in Hhi.
    split; [exact Hin|lia].
  - intros [Hin [Hlo Hhi]].
    split; [exact Hin|].
    apply andb_true_intro.
    split.
    + apply Z.leb_le. lia.
    + apply Z.ltb_lt. lia.
Qed.

Lemma positive_even_digit_cases : forall i,
  0 < i ->
  i < 10 ->
  Z.even i = true ->
  i = 2 \/ i = 4 \/ i = 6 \/ i = 8.
Proof.
  intros i Hpos Hlt Heven.
  apply Z.even_spec in Heven.
  destruct Heven as [k Hk].
  assert (1 <= k <= 4) by lia.
  lia.
Qed.

Lemma mod2_zero_even_true : forall i,
  i mod 2 = 0 ->
  Z.even i = true.
Proof.
  intros i Hmod.
  rewrite Zeven_mod.
  apply Zeq_is_eq_bool.
  exact Hmod.
Qed.

Lemma mod2_nonzero_even_false : forall i,
  i mod 2 <> 0 ->
  Z.even i <> true.
Proof.
  intros i Hmod Heven.
  apply Hmod.
  rewrite Zmod_even.
  rewrite Heven.
  reflexivity.
Qed.

Lemma generate_list_original_spec_163 : forall a b,
  0 < a ->
  0 < b ->
  problem_163_spec a b (generate_list (Z.min a b) (Z.max a b)).
Proof.
  intros a b Ha Hb.
  unfold problem_163_spec.
  split.
  - intros d.
    rewrite generate_prefix_list_in_163.
    split.
    + intros [Hin [Hlo Hhi]].
      destruct Hin as [Hin | [Hin | [Hin | [Hin | []]]]];
        subst d; repeat split; try lia.
    + intros [[Hlo Hhi] [Hlt Hmod]].
      assert (Hpos : 0 < d) by (pose proof (Z.le_min_l a b); pose proof (Z.le_min_r a b); lia).
      pose proof (positive_even_digit_cases d Hpos Hlt (mod2_zero_even_true d Hmod)) as Hcases.
      destruct Hcases as [Hd | [Hd | [Hd | Hd]]]; subst d.
      * split; [simpl; tauto | lia].
      * split; [simpl; tauto | lia].
      * split; [simpl; tauto | lia].
      * split; [simpl; tauto | lia].
  - split.
    + unfold generate_list, generate_prefix_list, digit_candidates.
      simpl.
      repeat match goal with
      | |- context [Z.leb ?x ?y] => destruct (Z.leb x y) eqn:?; simpl
      | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) eqn:?; simpl
      end;
      repeat constructor; simpl; lia.
    + unfold generate_list, generate_prefix_list, digit_candidates.
      simpl.
      repeat match goal with
      | |- context [Z.leb ?x ?y] => destruct (Z.leb x y) eqn:?; simpl
      | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) eqn:?; simpl
      end;
      repeat constructor; simpl; lia.
Qed.

Lemma generate_prefix_init : forall lo hi,
  0 < lo ->
  lo <= hi + 1 ->
  generate_prefix lo lo hi nil.
Proof.
  intros.
  unfold generate_prefix, generate_prefix_list, digit_candidates.
  split; [lia|].
  simpl.
  repeat match goal with
  | |- context [Z.leb ?x ?y] => destruct (Z.leb x y) eqn:?; try apply Z.leb_le in Heqb; try apply Z.leb_gt in Heqb
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) eqn:?; try apply Z.ltb_lt in Heqb; try apply Z.ltb_ge in Heqb
  end; simpl; try reflexivity; lia.
Qed.

Lemma generate_prefix_take : forall lo i hi output,
  0 < lo ->
  generate_prefix lo i hi output ->
  lo <= i <= hi ->
  i < 10 ->
  Z.even i = true ->
  generate_prefix lo (i + 1) hi (output ++ [i]).
Proof.
  intros lo i hi output Hlo [Hbounds Hout] Hi Hlt Heven.
  subst output.
  pose proof (positive_even_digit_cases i ltac:(lia) Hlt Heven) as Hcases.
  unfold generate_prefix, generate_prefix_list, digit_candidates in *.
  split; [lia|].
  destruct Hcases as [-> | [-> | [-> | ->]]];
    simpl;
    repeat match goal with
    | |- context [Z.leb ?x ?y] => destruct (Z.leb x y) eqn:?; try apply Z.leb_le in Heqb; try apply Z.leb_gt in Heqb
    | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) eqn:?; try apply Z.ltb_lt in Heqb; try apply Z.ltb_ge in Heqb
    end;
    simpl; try lia; reflexivity.
Qed.

Lemma generate_prefix_skip : forall lo i hi output,
  0 < lo ->
  generate_prefix lo i hi output ->
  lo <= i <= hi ->
  ~ (i < 10 /\ Z.even i = true) ->
  generate_prefix lo (i + 1) hi output.
Proof.
  intros lo i hi output Hlo [Hbounds Hout] Hi Hskip.
  subst output.
  unfold generate_prefix, generate_prefix_list, digit_candidates in *.
  split; [lia|].
  simpl.
  repeat match goal with
  | |- context [Z.leb ?x ?y] => destruct (Z.leb x y) eqn:?; try apply Z.leb_le in Heqb; try apply Z.leb_gt in Heqb
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) eqn:?; try apply Z.ltb_lt in Heqb; try apply Z.ltb_ge in Heqb
  end;
  simpl; try reflexivity;
  exfalso; apply Hskip; split; try lia;
  assert (i = 2 \/ i = 4 \/ i = 6 \/ i = 8) by lia;
  destruct H as [-> | [-> | [-> | ->]]]; reflexivity.
Qed.

Lemma generate_prefix_full_spec : forall a0 b0 lo hi output,
  0 < a0 ->
  0 < b0 ->
  generate_bounds a0 b0 lo hi ->
  generate_prefix lo (hi + 1) hi output ->
  problem_163_spec a0 b0 output.
Proof.
  intros a0 b0 lo hi output Ha0 Hb0 [Hlo Hhi] [_ Hout].
  subst lo hi output.
  apply generate_list_original_spec_163; assumption.
Qed.

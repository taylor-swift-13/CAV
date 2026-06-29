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
From SimpleC.EE.CAV.ground_truth_p163_generate_integers Require Import p163_generate_integers_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import Lia.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p163_generate_integers.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p163_generate_integers.v so public contract files expose definitions only. *)

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


Lemma proof_of_p163_generate_integers_safety_wit_15 : p163_generate_integers_safety_wit_15.
Proof.
  pre_process.
  entailer!.
  - unfold generate_bounds in *.
    destruct H6 as [Ha _].
    subst a.
    pose proof (Z.le_min_l a0 b0).
    lia.
  - unfold generate_bounds in *.
    destruct H6 as [_ Hb].
    subst b.
    assert (Z.max a0 b0 < INT_MAX) by (apply Z.max_lub_lt; lia).
    lia.
Qed.

Lemma proof_of_p163_generate_integers_entail_wit_1_1 : p163_generate_integers_entail_wit_1_1.
Proof.
  pre_process.
  Exists (@nil Z).
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
  - apply generate_prefix_init; lia.
  - unfold generate_bounds.
    subst a_pre b_pre.
    rewrite Z.min_l by lia.
    rewrite Z.max_r by lia.
    split; reflexivity.
Qed.

Lemma proof_of_p163_generate_integers_entail_wit_1_2 : p163_generate_integers_entail_wit_1_2.
Proof.
  pre_process.
  Exists (@nil Z).
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
  - apply generate_prefix_init; lia.
  - unfold generate_bounds.
    subst a_pre b_pre.
    rewrite Z.min_r by lia.
    rewrite Z.max_l by lia.
    split; reflexivity.
Qed.

Lemma proof_of_p163_generate_integers_entail_wit_2 : p163_generate_integers_entail_wit_2.
Proof.
  pre_process.
  Exists output_l_2.
  subst capacity.
  entailer!.
  all: try match goal with
  | H : generate_bounds _ _ _ _ |- _ =>
      unfold generate_bounds in H; destruct H as [Ha Hb]; subst;
      pose proof (Z.le_min_l a0 b0); pose proof (Z.le_min_r a0 b0); lia
  end.
Qed.

Lemma proof_of_p163_generate_integers_entail_wit_3 : p163_generate_integers_entail_wit_3.
Proof.
  pre_process.
  Exists (output_l_2 ++ (i :: nil)).
  subst capacity.
  entailer!.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - apply generate_prefix_take; try lia.
    + match goal with
      | H : generate_bounds a0 b0 a b |- _ =>
          unfold generate_bounds in H; destruct H as [Ha _]
      end.
      subst a.
      pose proof (Z.le_min_l a0 b0).
      pose proof (Z.le_min_r a0 b0).
      lia.
    + match goal with H : generate_prefix a i b output_l_2 |- _ => exact H end.
    + apply mod2_zero_even_true.
      rewrite <- Z.rem_mod_nonneg by (
        try lia;
        unfold generate_bounds in H6; destruct H6 as [Ha _]; subst a;
        pose proof (Z.le_min_l a0 b0);
        pose proof (Z.le_min_r a0 b0);
        lia).
      exact H11.
Qed.

Lemma proof_of_p163_generate_integers_entail_wit_4_2 : p163_generate_integers_entail_wit_4_2.
Proof.
  pre_process.
  Exists output_l_2.
  subst capacity.
  entailer!.
  apply generate_prefix_skip.
  - unfold generate_bounds in H8.
    destruct H8 as [Ha _].
    subst a.
    pose proof (Z.le_min_l a0 b0).
    pose proof (Z.le_min_r a0 b0).
    lia.
  - exact H14.
  - lia.
  - intros [Hlt _]. lia.
Qed.

Lemma proof_of_p163_generate_integers_entail_wit_4_3 : p163_generate_integers_entail_wit_4_3.
Proof.
  pre_process.
  Exists output_l_2.
  subst capacity.
  entailer!.
  apply generate_prefix_skip.
  - unfold generate_bounds in H9.
    destruct H9 as [Ha _].
    subst a.
    pose proof (Z.le_min_l a0 b0).
    pose proof (Z.le_min_r a0 b0).
    lia.
  - exact H15.
  - lia.
  - intros [_ Heven].
    apply (mod2_nonzero_even_false i).
    + intro Hmod.
      apply H.
      rewrite Z.rem_mod_nonneg by (
        try lia;
        unfold generate_bounds in H9; destruct H9 as [Ha _]; subst a;
        pose proof (Z.le_min_l a0 b0);
        pose proof (Z.le_min_r a0 b0);
        lia).
      exact Hmod.
    + exact Heven.
Qed.

Lemma proof_of_p163_generate_integers_entail_wit_6 : p163_generate_integers_entail_wit_6.
Proof.
  pre_process.
  Exists output_l_2.
  subst capacity.
  entailer!.
  - assert (i = b + 1) by lia.
    subst i.
    exact H13.
  - pose proof (generate_prefix_length_le_4 a i b output_l_2 H13).
    lia.
Qed.

Lemma proof_of_p163_generate_integers_return_wit_1 : p163_generate_integers_return_wit_1.
Proof.
  pre_process.
  Exists output_l_2 10 output_size_2 data_2.
  entailer!.
  apply generate_prefix_full_spec with (lo := a) (hi := b); try assumption; lia.
Qed.

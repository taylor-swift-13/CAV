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
From SimpleC.EE.CAV.ground_truth_p006_parse_nested_parens Require Import p006_parse_nested_parens_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Strings.Ascii.
Require Import Arith.
Require Import PeanoNat.

Import naive_C_Rules.
Require Import p006_parse_nested_parens.
Local Open Scope sac.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope list_scope.

(* Proof helpers moved from p006_parse_nested_parens.v so public contract files expose definitions only. *)

Lemma paren_scan_aux_step : forall prefix ch out in_group level max_level,
  paren_scan_aux (prefix ++ [ch]) out in_group level max_level =
  let st := paren_scan_aux prefix out in_group level max_level in
  paren_scan_aux [ch]
    (paren_state_out st)
    (paren_state_in_group st)
    (paren_state_level st)
    (paren_state_max st).
Proof.
  induction prefix as [| h t IH]; intros ch out in_group level max_level; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma paren_scan_aux_one : forall ch out in_group level max_level,
  paren_scan_aux [ch] out in_group level max_level =
  (paren_step_output out in_group max_level ch,
   paren_step_in_group in_group ch,
   paren_step_level in_group level ch,
   paren_step_max in_group level max_level ch).
Proof.
  reflexivity.
Qed.
Lemma paren_prefix_step : forall input i,
  0 <= i < Zlength input ->
  paren_prefix_output (i + 1) input =
    paren_step_output
      (paren_prefix_output i input)
      (paren_prefix_in_group i input)
      (paren_prefix_max i input)
      (Znth i input 0) /\
  paren_prefix_in_group (i + 1) input =
    paren_step_in_group
      (paren_prefix_in_group i input)
      (Znth i input 0) /\
  paren_prefix_level (i + 1) input =
    paren_step_level
      (paren_prefix_in_group i input)
      (paren_prefix_level i input)
      (Znth i input 0) /\
  paren_prefix_max (i + 1) input =
    paren_step_max
      (paren_prefix_in_group i input)
      (paren_prefix_level i input)
      (paren_prefix_max i input)
      (Znth i input 0).
Proof.
  intros input i Hi.
  unfold paren_prefix_output, paren_prefix_in_group,
    paren_prefix_level, paren_prefix_max, paren_prefix_state.
  assert (sublist 0 (i + 1) input = sublist 0 i input ++ [Znth i input 0]) as Hsub.
  {
    rewrite (sublist_split 0 (i + 1) i input)
      by (try rewrite Zlength_correct in *; lia).
    rewrite (sublist_single 0 i input) by lia.
    reflexivity.
  }
  rewrite Hsub.
  rewrite paren_scan_aux_step.
  rewrite paren_scan_aux_one.
  repeat split; reflexivity.
Qed.
Lemma paren_prefix_step_app : forall input i,
  0 <= i < Zlength input ->
  paren_prefix_output (i + 1) input =
    paren_step_output
      (paren_prefix_output i input)
      (paren_prefix_in_group i input)
      (paren_prefix_max i input)
      (Znth i (app input (cons 0 nil)) 0) /\
  paren_prefix_in_group (i + 1) input =
    paren_step_in_group
      (paren_prefix_in_group i input)
      (Znth i (app input (cons 0 nil)) 0) /\
  paren_prefix_level (i + 1) input =
    paren_step_level
      (paren_prefix_in_group i input)
      (paren_prefix_level i input)
      (Znth i (app input (cons 0 nil)) 0) /\
  paren_prefix_max (i + 1) input =
    paren_step_max
      (paren_prefix_in_group i input)
      (paren_prefix_level i input)
      (paren_prefix_max i input)
      (Znth i (app input (cons 0 nil)) 0).
Proof.
  intros input i Hi.
  pose proof (paren_prefix_step input i Hi) as Hstep.
  replace (Znth i (app input (cons 0 nil)) 0) with (Znth i input 0).
  - exact Hstep.
  - rewrite app_Znth1; lia.
Qed.
Lemma paren_prefix_full_final : forall input len,
  len = Zlength input ->
  paren_final_output
    (paren_prefix_output len input)
    (paren_prefix_in_group len input)
    (paren_prefix_max len input) =
  paren_output input.
Proof.
  intros input len Hlen.
  unfold paren_prefix_output, paren_prefix_in_group,
    paren_prefix_max, paren_prefix_state, paren_output.
  rewrite (sublist_self input len Hlen).
  destruct (paren_scan_aux input [] 0 0 0) as [[[out in_group] level] max_level].
  reflexivity.
Qed.
Lemma paren_step_level_nonneg : forall in_group level ch,
  0 <= level ->
  0 <= paren_step_level in_group level ch.
Proof.
  intros in_group level ch Hlevel.
  unfold paren_step_level.
  destruct (Z.eqb ch 32).
  - destruct (Z.eqb in_group 0); lia.
  - destruct (Z.eqb ch 40).
    + lia.
    + destruct (Z.ltb_spec 0 level); lia.
Qed.
Lemma paren_scan_aux_level_nonneg : forall chars out in_group level max_level,
  0 <= level ->
  0 <= paren_state_level (paren_scan_aux chars out in_group level max_level).
Proof.
  induction chars as [| ch rest IH]; intros out in_group level max_level Hlevel.
  - simpl. lia.
  - simpl.
    apply IH.
    apply paren_step_level_nonneg.
    exact Hlevel.
Qed.
Lemma paren_prefix_level_nonneg : forall i input,
  0 <= i ->
  0 <= paren_prefix_level i input.
Proof.
  intros i input Hi.
  unfold paren_prefix_level, paren_prefix_state.
  apply paren_scan_aux_level_nonneg.
  lia.
Qed.


Ltac prepare_paren_prefix_step :=
  let Hout := fresh "Hout" in
  let Hin := fresh "Hin" in
  let Hlevel := fresh "Hlevel" in
  let Hmax := fresh "Hmax" in
  match goal with
  | |- context [paren_prefix_output (?i + 1) ?l] =>
      pose proof (paren_prefix_step_app l i ltac:(lia)) as [Hout [Hin [Hlevel Hmax]]]
  end;
  rewrite Hout, Hin, Hlevel, Hmax;
  repeat match goal with
  | H : ?output_l = paren_prefix_output ?i ?l |- context[paren_prefix_output ?i ?l] =>
      replace (paren_prefix_output i l) with output_l by congruence
  | H : ?in_group = paren_prefix_in_group ?i ?l |- context[paren_prefix_in_group ?i ?l] =>
      replace (paren_prefix_in_group i l) with in_group by congruence
  | H : ?level = paren_prefix_level ?i ?l |- context[paren_prefix_level ?i ?l] =>
      replace (paren_prefix_level i l) with level by congruence
  | H : ?max_level = paren_prefix_max ?i ?l |- context[paren_prefix_max ?i ?l] =>
      replace (paren_prefix_max i l) with max_level by congruence
  end;
  repeat match goal with
  | H : Znth ?i (app ?l (cons 0 nil)) 0 = ?v |- _ => rewrite H
  end;
  cbn;
  unfold paren_step_output, paren_step_in_group, paren_step_level,
    paren_step_max, paren_final_output in *;
  cbn;
  repeat match goal with
  | H : ?x = 0 |- context[Z.eqb ?x 0] => rewrite H
  | H : 0 = ?x |- context[Z.eqb ?x 0] => rewrite <- H
  | H : ?x = 1 |- context[Z.eqb ?x 0] => rewrite H
  | H : 1 = ?x |- context[Z.eqb ?x 0] => rewrite <- H
  | H : ?x = 32 |- context[Z.eqb ?x 32] => rewrite H
  | H : 32 = ?x |- context[Z.eqb ?x 32] => rewrite <- H
  | H : ?x = 40 |- context[Z.eqb ?x 40] => rewrite H
  | H : 40 = ?x |- context[Z.eqb ?x 40] => rewrite <- H
  end;
  cbn;
  repeat match goal with
  | |- context[Z.eqb ?x ?x] => rewrite Z.eqb_refl
  end.

Lemma proof_of_p006_parse_nested_parens_entail_wit_1 : p006_parse_nested_parens_entail_wit_1.
Proof.
  pre_process; try subst orig; subst retval_3.
  Exists (@nil Z) 0.
  sep_apply (IntArray.undef_full_split_to_undef_seg retval_2 0 len).
  2: { lia. }
  rewrite (IntArray.undef_seg_empty retval_2 0).
  rewrite (IntArray.seg_empty retval_2 0 0).
  entailer!.
  all: unfold paren_prefix_output, paren_prefix_in_group,
    paren_prefix_level, paren_prefix_max, paren_prefix_state;
    try (rewrite (sublist_nil l 0 0) by lia); simpl; reflexivity.
Qed.

Lemma proof_of_p006_parse_nested_parens_entail_wit_2_1 : p006_parse_nested_parens_entail_wit_2_1.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    paren_prefix_output (i + 1) l = app output_l_2 (max_level :: nil) /\
    paren_prefix_in_group (i + 1) l = 0 /\
    paren_prefix_level (i + 1) l = 0 /\
    paren_prefix_max (i + 1) l = 0).
  {
    prepare_paren_prefix_step.
    try rewrite Z.eqb_refl.
    replace (Z.eqb in_group 0) with false by (symmetry; apply Z.eqb_neq; lia).
    repeat split; reflexivity.
  }
  destruct Hnext as [Hout [Hin [Hlevel Hmax]]].
  Exists (app output_l_2 (max_level :: nil)) (output_size_2 + 1).
  entailer!.
  all: try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_p006_parse_nested_parens_entail_wit_2_2 : p006_parse_nested_parens_entail_wit_2_2.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    paren_prefix_output (i + 1) l = output_l_2 /\
    paren_prefix_in_group (i + 1) l = in_group /\
    paren_prefix_level (i + 1) l = level /\
    paren_prefix_max (i + 1) l = max_level).
  {
    prepare_paren_prefix_step.
    subst in_group.
    try rewrite Z.eqb_refl.
    repeat split; reflexivity.
  }
  destruct Hnext as [Hout [Hin [Hlevel Hmax]]].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_p006_parse_nested_parens_entail_wit_2_3 : p006_parse_nested_parens_entail_wit_2_3.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    paren_prefix_output (i + 1) l = output_l_2 /\
    paren_prefix_in_group (i + 1) l = 1 /\
    paren_prefix_level (i + 1) l = level + 1 /\
    paren_prefix_max (i + 1) l = level + 1).
  {
    prepare_paren_prefix_step.
    replace (Z.eqb 40 32) with false by reflexivity.
    replace (Z.eqb 40 40) with true by reflexivity.
    unfold paren_zmax.
    destruct (Z.leb_spec max_level (level + 1)).
    - repeat split; reflexivity.
    - lia.
  }
  destruct Hnext as [Hout [Hin [Hlevel Hmax]]].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_p006_parse_nested_parens_entail_wit_2_4 : p006_parse_nested_parens_entail_wit_2_4.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    paren_prefix_output (i + 1) l = output_l_2 /\
    paren_prefix_in_group (i + 1) l = 1 /\
    paren_prefix_level (i + 1) l = level + 1 /\
    paren_prefix_max (i + 1) l = max_level).
  {
    prepare_paren_prefix_step.
    replace (Z.eqb 40 32) with false by reflexivity.
    replace (Z.eqb 40 40) with true by reflexivity.
    unfold paren_zmax.
    destruct (Z.leb_spec max_level (level + 1)).
    - repeat split; try reflexivity; lia.
    - repeat split; reflexivity.
  }
  destruct Hnext as [Hout [Hin [Hlevel Hmax]]].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_p006_parse_nested_parens_entail_wit_2_5 : p006_parse_nested_parens_entail_wit_2_5.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    paren_prefix_output (i + 1) l = output_l_2 /\
    paren_prefix_in_group (i + 1) l = 1 /\
    paren_prefix_level (i + 1) l = level - 1 /\
    paren_prefix_max (i + 1) l = max_level).
  {
    prepare_paren_prefix_step.
    replace (Z.eqb (Znth i (app l (cons 0 nil)) 0) 32) with false
      by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.eqb (Znth i (app l (cons 0 nil)) 0) 40) with false
      by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.ltb 0 level) with true by (symmetry; apply Z.ltb_lt; lia).
    repeat split; reflexivity.
  }
  destruct Hnext as [Hout [Hin [Hlevel Hmax]]].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_p006_parse_nested_parens_entail_wit_2_6 : p006_parse_nested_parens_entail_wit_2_6.
Proof.
  pre_process; try subst orig.
  assert (level = 0).
  {
    pose proof (paren_prefix_level_nonneg i l ltac:(lia)).
    lia.
  }
  subst level.
  assert (Hnext:
    paren_prefix_output (i + 1) l = output_l_2 /\
    paren_prefix_in_group (i + 1) l = 1 /\
    paren_prefix_level (i + 1) l = 0 /\
    paren_prefix_max (i + 1) l = max_level).
  {
    prepare_paren_prefix_step.
    replace (Z.eqb (Znth i (app l (cons 0 nil)) 0) 32) with false
      by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.eqb (Znth i (app l (cons 0 nil)) 0) 40) with false
      by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.ltb 0 (paren_prefix_level i l)) with false
      by (symmetry; apply Z.ltb_ge; lia).
    repeat split; reflexivity.
  }
  destruct Hnext as [Hout [Hin [Hlevel Hmax]]].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_p006_parse_nested_parens_entail_wit_3 : p006_parse_nested_parens_entail_wit_3.
Proof.
  pre_process; try subst orig.
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_p006_parse_nested_parens_entail_wit_4_1 : p006_parse_nested_parens_entail_wit_4_1.
Proof.
  pre_process; try subst orig.
  assert (i = len) by lia; subst i.
  assert (in_group = 1) by lia.
  assert (Hout:
    paren_final_output (paren_prefix_output len l)
      (paren_prefix_in_group len l) (paren_prefix_max len l) =
    app output_l_2 (max_level :: nil)).
  {
    subst in_group.
    unfold paren_final_output.
    replace (paren_prefix_in_group len l) with 1 by congruence.
    cbn.
    replace (paren_prefix_output len l) with output_l_2 by congruence.
    replace (paren_prefix_max len l) with max_level by congruence.
    reflexivity.
  }
  Exists (app output_l_2 (max_level :: nil)) (output_size_2 + 1).
  entailer!.
  all: try rewrite Hout; try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_p006_parse_nested_parens_entail_wit_4_2 : p006_parse_nested_parens_entail_wit_4_2.
Proof.
  pre_process; try subst orig.
  assert (i = len) by lia; subst i.
  assert (Hout:
    paren_final_output (paren_prefix_output len l)
      (paren_prefix_in_group len l) (paren_prefix_max len l) =
    output_l_2).
  {
    subst in_group.
    unfold paren_final_output.
    replace (paren_prefix_in_group len l) with 0 by congruence.
    cbn.
    congruence.
  }
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_p006_parse_nested_parens_return_wit_1 : p006_parse_nested_parens_return_wit_1.
Proof.
  pre_process; try subst orig.
  Exists data_2 output_l_2 output_size_2.
  entailer!.
  subst output_l_2.
  rewrite paren_prefix_full_final by lia.
  unfold problem_6_spec.
  reflexivity.
Qed.

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
From SimpleC.EE.CAV.ground_truth_p017_parse_music Require Import p017_parse_music_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Ascii String List.

Import naive_C_Rules.
Require Import p017_parse_music.
Local Open Scope sac.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope list_scope.

(* Proof helpers moved from p017_parse_music.v so public contract files expose definitions only. *)

Lemma music_prefix_full_final : forall input len,
  len = Zlength input ->
  music_final_output
    (music_prefix_output len input)
    (music_prefix_state len input) =
  music_output input.
Proof.
  intros input len Hlen.
  unfold music_prefix_output, music_prefix_state, music_output.
  rewrite (sublist_self input len Hlen).
  reflexivity.
Qed.
Lemma music_scan_aux_step : forall prefix ch out state,
  music_scan_aux (prefix ++ [ch]) out state =
  let scanned := music_scan_aux prefix out state in
  (music_step_output (fst scanned) (snd scanned) ch,
   note_state_step (snd scanned) ch).
Proof.
  induction prefix as [| h t IH]; intros ch out state; simpl.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.
Lemma music_prefix_step : forall input i,
  0 <= i < Zlength input ->
  music_prefix_output (i + 1) input =
    music_step_output
      (music_prefix_output i input)
      (music_prefix_state i input)
      (Znth i input 0) /\
  music_prefix_state (i + 1) input =
    note_state_step
      (music_prefix_state i input)
      (Znth i input 0).
Proof.
  intros input i Hi.
  unfold music_prefix_output, music_prefix_state.
  assert (sublist 0 (i + 1) input = sublist 0 i input ++ [Znth i input 0]) as Hsub.
  {
    rewrite (sublist_split 0 (i + 1) i input) by lia.
    rewrite (sublist_single 0 i input) by lia.
    reflexivity.
  }
  rewrite Hsub.
  rewrite music_scan_aux_step.
  split; reflexivity.
Qed.
Lemma music_prefix_step_app : forall input i,
  0 <= i < Zlength input ->
  music_prefix_output (i + 1) input =
    music_step_output
      (music_prefix_output i input)
      (music_prefix_state i input)
      (Znth i (app input (cons 0 nil)) 0) /\
  music_prefix_state (i + 1) input =
    note_state_step
      (music_prefix_state i input)
      (Znth i (app input (cons 0 nil)) 0).
Proof.
  intros input i Hi.
  pose proof (music_prefix_step input i Hi) as [Hout Hstate].
  replace (Znth i (app input (cons 0 nil)) 0) with (Znth i input 0).
  - split; assumption.
  - rewrite app_Znth1; lia.
Qed.
Lemma note_state_step_range : forall state ch,
  0 <= state <= 5 ->
  0 <= note_state_step state ch <= 5.
Proof.
  intros state ch Hstate.
  unfold note_state_step.
  destruct (Z.eqb ch 32) eqn:?; [lia |].
  destruct (Z.eqb state 0) eqn:?.
  - destruct (Z.eqb ch 111) eqn:?; [lia |].
    destruct (Z.eqb ch 46) eqn:?; lia.
  - destruct (Z.eqb state 1) eqn:?.
    + destruct (Z.eqb ch 124) eqn:?; lia.
    + destruct (Z.eqb state 3) eqn:?.
      * destruct (Z.eqb ch 124) eqn:?; lia.
      * lia.
Qed.
Lemma music_step_space_skip : forall out state,
  state <> 1 -> state <> 2 -> state <> 4 ->
  music_step_output out state 32 = out /\
  note_state_step state 32 = 0.
Proof.
  intros out state H1 H2 H4.
  unfold music_step_output, music_final_output, note_state_step.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq state 1) H1).
  rewrite (proj2 (Z.eqb_neq state 2) H2).
  rewrite (proj2 (Z.eqb_neq state 4) H4).
  split; reflexivity.
Qed.
Lemma music_step_space_1 : forall out,
  music_step_output out 1 32 = out ++ [4] /\
  note_state_step 1 32 = 0.
Proof.
  intros out.
  unfold music_step_output, music_final_output, note_state_step.
  repeat rewrite Z.eqb_refl.
  split; reflexivity.
Qed.
Lemma music_step_space_2 : forall out,
  music_step_output out 2 32 = out ++ [2] /\
  note_state_step 2 32 = 0.
Proof.
  intros out.
  unfold music_step_output, music_final_output, note_state_step.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq 2 1) ltac:(lia)).
  split; reflexivity.
Qed.
Lemma music_step_space_4 : forall out,
  music_step_output out 4 32 = out ++ [1] /\
  note_state_step 4 32 = 0.
Proof.
  intros out.
  unfold music_step_output, music_final_output, note_state_step.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq 4 1) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq 4 2) ltac:(lia)).
  split; reflexivity.
Qed.
Lemma music_step_nonspace_0_o : forall out,
  music_step_output out 0 111 = out /\
  note_state_step 0 111 = 1.
Proof.
  intros out.
  unfold music_step_output, note_state_step.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq 111 32) ltac:(lia)).
  split; reflexivity.
Qed.
Lemma music_step_nonspace_0_dot : forall out,
  music_step_output out 0 46 = out /\
  note_state_step 0 46 = 3.
Proof.
  intros out.
  unfold music_step_output, note_state_step.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq 46 32) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq 46 111) ltac:(lia)).
  split; reflexivity.
Qed.
Lemma music_step_nonspace_1_bar : forall out,
  music_step_output out 1 124 = out /\
  note_state_step 1 124 = 2.
Proof.
  intros out.
  unfold music_step_output, note_state_step.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq 124 32) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq 1 0) ltac:(lia)).
  split; reflexivity.
Qed.
Lemma music_step_nonspace_3_bar : forall out,
  music_step_output out 3 124 = out /\
  note_state_step 3 124 = 4.
Proof.
  intros out.
  unfold music_step_output, note_state_step.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq 124 32) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq 3 0) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq 3 1) ltac:(lia)).
  split; reflexivity.
Qed.
Lemma music_step_nonspace_3_bad : forall out ch,
  ch <> 32 -> ch <> 124 ->
  music_step_output out 3 ch = out /\
  note_state_step 3 ch = 5.
Proof.
  intros out ch Hspace Hbar.
  unfold music_step_output, note_state_step.
  rewrite (proj2 (Z.eqb_neq ch 32) Hspace).
  rewrite (proj2 (Z.eqb_neq 3 0) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq 3 1) ltac:(lia)).
  rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq ch 124) Hbar).
  split; reflexivity.
Qed.
Lemma music_step_nonspace_1_bad : forall out ch,
  ch <> 32 -> ch <> 124 ->
  music_step_output out 1 ch = out /\
  note_state_step 1 ch = 5.
Proof.
  intros out ch Hspace Hbar.
  unfold music_step_output, note_state_step.
  rewrite (proj2 (Z.eqb_neq ch 32) Hspace).
  rewrite (proj2 (Z.eqb_neq 1 0) ltac:(lia)).
  rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq ch 124) Hbar).
  split; reflexivity.
Qed.
Lemma music_step_nonspace_0_bad : forall out ch,
  ch <> 32 -> ch <> 111 -> ch <> 46 ->
  music_step_output out 0 ch = out /\
  note_state_step 0 ch = 5.
Proof.
  intros out ch Hspace Ho Hdot.
  unfold music_step_output, note_state_step.
  rewrite (proj2 (Z.eqb_neq ch 32) Hspace).
  rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq ch 111) Ho).
  rewrite (proj2 (Z.eqb_neq ch 46) Hdot).
  split; reflexivity.
Qed.
Lemma music_step_nonspace_other_bad : forall out state ch,
  ch <> 32 -> state <> 0 -> state <> 1 -> state <> 3 ->
  music_step_output out state ch = out /\
  note_state_step state ch = 5.
Proof.
  intros out state ch Hspace H0 H1 H3.
  unfold music_step_output, note_state_step.
  rewrite (proj2 (Z.eqb_neq ch 32) Hspace).
  rewrite (proj2 (Z.eqb_neq state 0) H0).
  rewrite (proj2 (Z.eqb_neq state 1) H1).
  rewrite (proj2 (Z.eqb_neq state 3) H3).
  split; reflexivity.
Qed.


Ltac prepare_music_prefix_step :=
  let Hprefix_out := fresh "Hprefix_out" in
  let Hprefix_state := fresh "Hprefix_state" in
  match goal with
  | |- context [music_prefix_output (?i + 1) ?l] =>
      pose proof (music_prefix_step_app l i ltac:(lia)) as [Hprefix_out Hprefix_state]
  end;
  rewrite Hprefix_out, Hprefix_state;
  repeat match goal with
  | H : ?output_l = music_prefix_output ?i ?l |- context[music_prefix_output ?i ?l] =>
      replace (music_prefix_output i l) with output_l by congruence
  end;
  repeat match goal with
  | H : ?state = music_prefix_state ?i ?l |- context[music_prefix_state ?i ?l] =>
      replace (music_prefix_state i l) with state by congruence
  end;
  repeat match goal with
  | H : Znth ?i (app ?l (cons 0 nil)) 0 = ?v |- _ => rewrite H
  end;
  repeat match goal with
  | H : ?s = ?v |- context[?s] =>
      let T := type of s in
      unify T Z;
      is_var s;
      rewrite H
  end.

Lemma proof_of_p017_parse_music_entail_wit_1 : p017_parse_music_entail_wit_1.
Proof.
  pre_process; try subst orig.
  Exists (@nil Z) 0.
  sep_apply (IntArray.undef_full_split_to_undef_seg retval_2 0 (retval_3 + 1)).
  2: { lia. }
  subst retval_3.
  rewrite (IntArray.undef_seg_empty retval_2 0).
  rewrite (IntArray.seg_empty retval_2 0 0).
  entailer!.
  all: try congruence; unfold music_prefix_output, music_prefix_state;
    try (rewrite (sublist_nil l 0 0) by lia); simpl; reflexivity.
Qed.

Lemma proof_of_p017_parse_music_entail_wit_2_1 : p017_parse_music_entail_wit_2_1.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output (i + 1) l = output_l_2 /\
    music_prefix_state (i + 1) l = 0).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state i l) with state by congruence.
    apply music_step_space_skip; congruence.
  }
  destruct Hnext as [Hout Hstate].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_p017_parse_music_entail_wit_2_2 : p017_parse_music_entail_wit_2_2.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output (i + 1) l = app output_l_2 (1 :: nil) /\
    music_prefix_state (i + 1) l = 0).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state i l) with state by congruence.
    subst state.
    apply music_step_space_4.
  }
  destruct Hnext as [Hout Hstate].
  Exists (app output_l_2 (1 :: nil)) (output_size_2 + 1).
  entailer!.
  all: try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_p017_parse_music_entail_wit_2_3 : p017_parse_music_entail_wit_2_3.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output (i + 1) l = app output_l_2 (2 :: nil) /\
    music_prefix_state (i + 1) l = 0).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state i l) with state by congruence.
    subst state.
    apply music_step_space_2.
  }
  destruct Hnext as [Hout Hstate].
  Exists (app output_l_2 (2 :: nil)) (output_size_2 + 1).
  entailer!.
  all: try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_p017_parse_music_entail_wit_2_4 : p017_parse_music_entail_wit_2_4.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output (i + 1) l = app output_l_2 (4 :: nil) /\
    music_prefix_state (i + 1) l = 0).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state i l) with state by congruence.
    subst state.
    apply music_step_space_1.
  }
  destruct Hnext as [Hout Hstate].
  Exists (app output_l_2 (4 :: nil)) (output_size_2 + 1).
  entailer!.
  all: try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_p017_parse_music_entail_wit_2_5 : p017_parse_music_entail_wit_2_5.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output (i + 1) l = output_l_2 /\
    music_prefix_state (i + 1) l = 1).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state i l) with state by congruence.
    subst state.
    apply music_step_nonspace_0_o.
  }
  destruct Hnext as [Hout Hstate].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_p017_parse_music_entail_wit_2_6 : p017_parse_music_entail_wit_2_6.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output (i + 1) l = output_l_2 /\
    music_prefix_state (i + 1) l = 3).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state i l) with state by congruence.
    subst state.
    apply music_step_nonspace_0_dot.
  }
  destruct Hnext as [Hout Hstate].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_p017_parse_music_entail_wit_2_7 : p017_parse_music_entail_wit_2_7.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output (i + 1) l = output_l_2 /\
    music_prefix_state (i + 1) l = 2).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state i l) with state by congruence.
    subst state.
    apply music_step_nonspace_1_bar.
  }
  destruct Hnext as [Hout Hstate].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_p017_parse_music_entail_wit_2_8 : p017_parse_music_entail_wit_2_8.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output (i + 1) l = output_l_2 /\
    music_prefix_state (i + 1) l = 4).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state i l) with state by congruence.
    subst state.
    apply music_step_nonspace_3_bar.
  }
  destruct Hnext as [Hout Hstate].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_p017_parse_music_entail_wit_2_9 : p017_parse_music_entail_wit_2_9.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output (i + 1) l = output_l_2 /\
    music_prefix_state (i + 1) l = 5).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state i l) with state by congruence.
    subst state.
    apply music_step_nonspace_3_bad; congruence.
  }
  destruct Hnext as [Hout Hstate].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_p017_parse_music_entail_wit_2_10 : p017_parse_music_entail_wit_2_10.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output (i + 1) l = output_l_2 /\
    music_prefix_state (i + 1) l = 5).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state i l) with state by congruence.
    subst state.
    apply music_step_nonspace_1_bad; congruence.
  }
  destruct Hnext as [Hout Hstate].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_p017_parse_music_entail_wit_2_11 : p017_parse_music_entail_wit_2_11.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output (i + 1) l = output_l_2 /\
    music_prefix_state (i + 1) l = 5).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state i l) with state by congruence.
    subst state.
    apply music_step_nonspace_0_bad; congruence.
  }
  destruct Hnext as [Hout Hstate].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_p017_parse_music_entail_wit_2_12 : p017_parse_music_entail_wit_2_12.
Proof.
  pre_process; try subst orig.
  assert (Hnext:
    music_prefix_output (i + 1) l = output_l_2 /\
    music_prefix_state (i + 1) l = 5).
  {
    prepare_music_prefix_step.
    replace (music_prefix_state i l) with state by congruence.
    apply music_step_nonspace_other_bad; congruence.
  }
  destruct Hnext as [Hout Hstate].
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_p017_parse_music_entail_wit_3 : p017_parse_music_entail_wit_3.
Proof.
  pre_process; try subst orig.
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_p017_parse_music_entail_wit_4_1 : p017_parse_music_entail_wit_4_1.
Proof.
  pre_process; try subst orig.
  assert (i = len) as -> by lia.
  assert (Hfinal:
    music_final_output (music_prefix_output len l) (music_prefix_state len l) =
    app output_l_2 (4 :: nil)).
  {
    match goal with H : output_l_2 = music_prefix_output len l |- _ => rewrite <- H end.
    match goal with H : state = music_prefix_state len l |- _ => rewrite <- H end.
    match goal with H : state = 1 |- _ => rewrite H end.
    unfold music_final_output.
    rewrite Z.eqb_refl.
    reflexivity.
  }
  Exists (app output_l_2 (4 :: nil)) (output_size_2 + 1).
  entailer!.
  all: try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_p017_parse_music_entail_wit_4_2 : p017_parse_music_entail_wit_4_2.
Proof.
  pre_process; try subst orig.
  assert (i = len) as -> by lia.
  assert (Hfinal:
    music_final_output (music_prefix_output len l) (music_prefix_state len l) =
    app output_l_2 (2 :: nil)).
  {
    match goal with H : output_l_2 = music_prefix_output len l |- _ => rewrite <- H end.
    match goal with H : state = music_prefix_state len l |- _ => rewrite <- H end.
    match goal with H : state = 2 |- _ => rewrite H end.
    unfold music_final_output.
    rewrite (proj2 (Z.eqb_neq 2 1) ltac:(lia)).
    rewrite Z.eqb_refl.
    reflexivity.
  }
  Exists (app output_l_2 (2 :: nil)) (output_size_2 + 1).
  entailer!.
  all: try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_p017_parse_music_entail_wit_4_3 : p017_parse_music_entail_wit_4_3.
Proof.
  pre_process; try subst orig.
  assert (i = len) as -> by lia.
  assert (Hfinal:
    music_final_output (music_prefix_output len l) (music_prefix_state len l) =
    app output_l_2 (1 :: nil)).
  {
    match goal with H : output_l_2 = music_prefix_output len l |- _ => rewrite <- H end.
    match goal with H : state = music_prefix_state len l |- _ => rewrite <- H end.
    match goal with H : state = 4 |- _ => rewrite H end.
    unfold music_final_output.
    rewrite (proj2 (Z.eqb_neq 4 1) ltac:(lia)).
    rewrite (proj2 (Z.eqb_neq 4 2) ltac:(lia)).
    rewrite Z.eqb_refl.
    reflexivity.
  }
  Exists (app output_l_2 (1 :: nil)) (output_size_2 + 1).
  entailer!.
  all: try rewrite Zlength_app; try rewrite Zlength_cons; try rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_p017_parse_music_entail_wit_4_4 : p017_parse_music_entail_wit_4_4.
Proof.
  pre_process; try subst orig.
  assert (i = len) as -> by lia.
  assert (Hfinal:
    music_final_output (music_prefix_output len l) (music_prefix_state len l) =
    output_l_2).
  {
    match goal with H : output_l_2 = music_prefix_output len l |- _ => rewrite <- H end.
    match goal with H : state = music_prefix_state len l |- _ => rewrite <- H end.
    unfold music_final_output.
    repeat match goal with
    | H : state <> ?v |- context [Z.eqb state ?v] =>
        rewrite (proj2 (Z.eqb_neq state v) H)
    end.
    reflexivity.
  }
  Exists output_l_2 output_size_2.
  entailer!.
Qed.

Lemma proof_of_p017_parse_music_return_wit_1 : p017_parse_music_return_wit_1.
Proof.
  pre_process; try subst orig.
  Exists data_2 output_l_2 output_size_2.
  entailer!.
  all: try solve [assumption | lia].
  all: try solve [
    unfold problem_17_spec;
    match goal with
    | H : ?out =
          music_final_output (music_prefix_output ?n ?input)
            (music_prefix_state ?n ?input) |- ?out = music_output ?input =>
        rewrite H; rewrite music_prefix_full_final by lia; reflexivity
    | H : music_final_output (music_prefix_output ?n ?input)
            (music_prefix_state ?n ?input) = ?out |- ?out = music_output ?input =>
        rewrite <- H; rewrite music_prefix_full_final by lia; reflexivity
    end
  ].
Qed.

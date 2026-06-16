Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260606_212531_p006_parse_nested_parens Require Import p006_parse_nested_parens_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p006_parse_nested_parens.
Local Open Scope sac.

(* ===== Helper Lemmas ===== *)

Lemma paren_scan_aux_app: forall (xs ys : list Z) (out : list Z) (ig lv ml : Z),
  paren_scan_aux (xs ++ ys) out ig lv ml =
  paren_scan_aux ys
    (paren_state_out (paren_scan_aux xs out ig lv ml))
    (paren_state_in_group (paren_scan_aux xs out ig lv ml))
    (paren_state_level (paren_scan_aux xs out ig lv ml))
    (paren_state_max (paren_scan_aux xs out ig lv ml)).
Proof.
  induction xs; intros; simpl.
  - reflexivity.
  - rewrite IHxs. reflexivity.
Qed.

Lemma paren_prefix_state_zero: forall l,
  paren_prefix_state 0 l = (@nil Z, 0, 0, 0).
Proof.
  intros. unfold paren_prefix_state.
  rewrite (Zsublist_nil l 0 0) by lia.
  simpl. reflexivity.
Qed.

Lemma paren_prefix_level_zero: forall l,
  paren_prefix_level 0 l = 0.
Proof.
  intros. unfold paren_prefix_level.
  rewrite paren_prefix_state_zero. simpl. reflexivity.
Qed.

Lemma paren_prefix_max_zero: forall l,
  paren_prefix_max 0 l = 0.
Proof.
  intros. unfold paren_prefix_max.
  rewrite paren_prefix_state_zero. simpl. reflexivity.
Qed.

Lemma paren_prefix_in_group_zero: forall l,
  paren_prefix_in_group 0 l = 0.
Proof.
  intros. unfold paren_prefix_in_group.
  rewrite paren_prefix_state_zero. simpl. reflexivity.
Qed.

Lemma paren_prefix_output_zero: forall l,
  paren_prefix_output 0 l = @nil Z.
Proof.
  intros. unfold paren_prefix_output.
  rewrite paren_prefix_state_zero. simpl. reflexivity.
Qed.

Lemma paren_prefix_state_step: forall i l,
  0 <= i -> i < Zlength l ->
  paren_prefix_state (i + 1) l =
  (paren_step_output (paren_prefix_output i l) (paren_prefix_in_group i l) (paren_prefix_max i l) (Znth i l 0),
   paren_step_in_group (paren_prefix_in_group i l) (Znth i l 0),
   paren_step_level (paren_prefix_in_group i l) (paren_prefix_level i l) (Znth i l 0),
   paren_step_max (paren_prefix_in_group i l) (paren_prefix_level i l) (paren_prefix_max i l) (Znth i l 0)).
Proof.
  intros i l Hi Hlt.
  unfold paren_prefix_state, paren_prefix_output, paren_prefix_in_group, paren_prefix_level, paren_prefix_max.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite paren_scan_aux_app.
  rewrite (sublist_single 0 i l) by lia.
  simpl. reflexivity.
Qed.

Lemma paren_prefix_level_step: forall i l,
  0 <= i -> i < Zlength l ->
  paren_prefix_level (i + 1) l =
  paren_step_level (paren_prefix_in_group i l) (paren_prefix_level i l) (Znth i l 0).
Proof.
  intros i l Hi Hlt.
  unfold paren_prefix_level.
  rewrite (paren_prefix_state_step i l Hi Hlt).
  simpl. reflexivity.
Qed.

Lemma paren_prefix_max_step: forall i l,
  0 <= i -> i < Zlength l ->
  paren_prefix_max (i + 1) l =
  paren_step_max (paren_prefix_in_group i l) (paren_prefix_level i l) (paren_prefix_max i l) (Znth i l 0).
Proof.
  intros i l Hi Hlt.
  unfold paren_prefix_max.
  rewrite (paren_prefix_state_step i l Hi Hlt).
  simpl. reflexivity.
Qed.

Lemma paren_prefix_in_group_step: forall i l,
  0 <= i -> i < Zlength l ->
  paren_prefix_in_group (i + 1) l =
  paren_step_in_group (paren_prefix_in_group i l) (Znth i l 0).
Proof.
  intros i l Hi Hlt.
  unfold paren_prefix_in_group.
  rewrite (paren_prefix_state_step i l Hi Hlt).
  simpl. reflexivity.
Qed.

Lemma paren_prefix_output_step: forall i l,
  0 <= i -> i < Zlength l ->
  paren_prefix_output (i + 1) l =
  paren_step_output (paren_prefix_output i l) (paren_prefix_in_group i l) (paren_prefix_max i l) (Znth i l 0).
Proof.
  intros i l Hi Hlt.
  unfold paren_prefix_output.
  rewrite (paren_prefix_state_step i l Hi Hlt).
  simpl. reflexivity.
Qed.

Lemma paren_output_eq: forall l,
  paren_output l =
  paren_final_output (paren_prefix_output (Zlength l) l)
                     (paren_prefix_in_group (Zlength l) l)
                     (paren_prefix_max (Zlength l) l).
Proof.
  intros.
  unfold paren_output, paren_prefix_output, paren_prefix_in_group, paren_prefix_max, paren_prefix_state.
  rewrite (sublist_self l (Zlength l)) by reflexivity.
  reflexivity.
Qed.

(* ===== Witness Proofs ===== *)

Lemma proof_of_p006_parse_nested_parens_entail_wit_1 : p006_parse_nested_parens_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z).
  split_pure_spatial.
  - (* spatial: convert undef_full -> undef_seg + empty seg *)
    rewrite Zlength_nil.
    match goal with H: retval_3 = len |- _ => rewrite <- H end.
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval_2 retval_3).
    rewrite (IntArray.seg_empty retval_2 0 0).
    match goal with H: paren_string_pre = orig |- _ => rewrite H end.
    cancel.
  - split_pures.
    + lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; rewrite paren_prefix_level_zero; reflexivity.
    + dump_pre_spatial; rewrite paren_prefix_max_zero; reflexivity.
    + dump_pre_spatial; rewrite paren_prefix_in_group_zero; reflexivity.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + dump_pre_spatial; rewrite paren_prefix_output_zero; reflexivity.
    + rewrite Zlength_nil; lia.
    + rewrite Zlength_nil; lia.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
Qed.

(* Helper: get character at position i from l, using the fact that
   Znth i (l ++ (0::nil)) 0 = Znth i l 0 when i < Zlength l *)
Ltac znth_app_to_l Hnth Hbound :=
  pose proof (app_Znth1 l (0::nil) i Hbound);
  congruence.

Lemma proof_of_p006_parse_nested_parens_entail_wit_2_1 : p006_parse_nested_parens_entail_wit_2_1.
Proof.
  pre_process.
  (* Premises: ch = 32 (space), in_group <> 0 *)
  (* Current state transitions: output_acc' = output_acc_2 ++ [max_level], in_group'=0, level'=0, max'=0 *)
  assert (Hlen: i < Zlength l) by (match goal with H: Zlength l = len |- _ => rewrite H; assumption end).
  assert (Hnth: Znth i l 0 = 32).
  { pose proof (app_Znth1 l (0::nil) i ltac:(lia)). congruence. }
  Exists (app output_acc_2 (cons max_level nil)).
  rewrite Zlength_app; simpl.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
    + (* 0 = paren_prefix_level (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_level_step by lia.
      match goal with
        Hlev: level = paren_prefix_level i l,
        Hig: in_group = paren_prefix_in_group i l |- _ =>
        rewrite <- Hlev, <- Hig, Hnth
      end.
      unfold paren_step_level. simpl.
      match goal with H: in_group <> 0 |- _ =>
        assert (Z.eqb in_group 0 = false) by (apply Z.eqb_neq; exact H);
        rewrite H0; reflexivity
      end.
    + (* 0 = paren_prefix_max (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_max_step by lia.
      match goal with
        Hlev: level = paren_prefix_level i l,
        Hig: in_group = paren_prefix_in_group i l,
        Hmax: max_level = paren_prefix_max i l |- _ =>
        rewrite <- Hlev, <- Hig, <- Hmax, Hnth
      end.
      unfold paren_step_max. simpl.
      match goal with H: in_group <> 0 |- _ =>
        assert (Z.eqb in_group 0 = false) by (apply Z.eqb_neq; exact H);
        rewrite H0; reflexivity
      end.
    + (* 0 = paren_prefix_in_group (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_in_group_step by lia.
      match goal with Hig: in_group = paren_prefix_in_group i l |- _ =>
        rewrite <- Hig, Hnth
      end.
      unfold paren_step_in_group. simpl. reflexivity.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + (* output_acc = paren_prefix_output (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_output_step by lia.
      match goal with
        Hout: output_acc_2 = paren_prefix_output i l,
        Hig: in_group = paren_prefix_in_group i l,
        Hmax: max_level = paren_prefix_max i l |- _ =>
        rewrite <- Hout, <- Hig, <- Hmax, Hnth
      end.
      unfold paren_step_output. simpl.
      unfold paren_final_output.
      match goal with H: in_group <> 0 |- _ =>
        assert (Z.eqb in_group 0 = false) by (apply Z.eqb_neq; exact H);
        rewrite H0; reflexivity
      end.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
Qed.

Lemma proof_of_p006_parse_nested_parens_entail_wit_2_2 : p006_parse_nested_parens_entail_wit_2_2.
Proof.
  pre_process.
  (* Premises: ch = 32 (space), in_group = 0 *)
  (* State stays the same: level, max_level, in_group all unchanged since in_group=0 *)
  assert (Hlen: i < Zlength l) by (match goal with H: Zlength l = len |- _ => rewrite H; assumption end).
  assert (Hnth: Znth i l 0 = 32).
  { pose proof (app_Znth1 l (0::nil) i ltac:(lia)). congruence. }
  Exists output_acc_2.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
    + (* level = paren_prefix_level (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_level_step by lia.
      match goal with
        Hlev: level = paren_prefix_level i l,
        Hig: in_group = paren_prefix_in_group i l,
        Hig0: in_group = 0 |- _ =>
        rewrite <- Hlev, <- Hig, Hnth;
        unfold paren_step_level; simpl;
        rewrite Hig0; simpl; exact Hlev
      end.
    + (* max_level = paren_prefix_max (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_max_step by lia.
      match goal with
        Hlev: level = paren_prefix_level i l,
        Hig: in_group = paren_prefix_in_group i l,
        Hmax: max_level = paren_prefix_max i l,
        Hig0: in_group = 0 |- _ =>
        rewrite <- Hlev, <- Hig, <- Hmax, Hnth;
        unfold paren_step_max; simpl;
        rewrite Hig0; simpl; exact Hmax
      end.
    + (* in_group = paren_prefix_in_group (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_in_group_step by lia.
      match goal with
        Hig: in_group = paren_prefix_in_group i l,
        Hig0: in_group = 0 |- _ =>
        rewrite <- Hig, Hnth;
        unfold paren_step_in_group; simpl;
        exact Hig0
      end.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + (* output_acc_2 = paren_prefix_output (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_output_step by lia.
      match goal with
        Hout: output_acc_2 = paren_prefix_output i l,
        Hig: in_group = paren_prefix_in_group i l,
        Hmax: max_level = paren_prefix_max i l,
        Hig0: in_group = 0 |- _ =>
        rewrite <- Hout, <- Hig, <- Hmax, Hnth;
        unfold paren_step_output; simpl;
        rewrite Hig0;
        unfold paren_final_output; simpl;
        exact Hout
      end.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
Qed.

Lemma proof_of_p006_parse_nested_parens_entail_wit_2_3 : p006_parse_nested_parens_entail_wit_2_3.
Proof.
  pre_process.
  (* Premises: ch = 40 ('('), level+1 > max_level *)
  assert (Hlen: i < Zlength l) by (match goal with H: Zlength l = len |- _ => rewrite H; assumption end).
  assert (Hnth: Znth i l 0 = 40).
  { pose proof (app_Znth1 l (0::nil) i ltac:(lia)). congruence. }
  Exists output_acc_2.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
    + (* level+1 = paren_prefix_level (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_level_step by lia.
      match goal with
        Hlev: level = paren_prefix_level i l,
        Hig: in_group = paren_prefix_in_group i l |- _ =>
        rewrite <- Hlev, <- Hig, Hnth;
        unfold paren_step_level; simpl; lia
      end.
    + (* level+1 = paren_prefix_max (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_max_step by lia.
      match goal with
        Hlev: level = paren_prefix_level i l,
        Hig: in_group = paren_prefix_in_group i l,
        Hmax: max_level = paren_prefix_max i l,
        Hgt: (level + 1) > max_level |- _ =>
        rewrite <- Hlev, <- Hig, <- Hmax, Hnth;
        unfold paren_step_max; simpl;
        unfold paren_zmax;
        destruct (Z.leb_spec max_level (level + 1));
        [lia | lia]
      end.
    + (* 1 = paren_prefix_in_group (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_in_group_step by lia.
      match goal with Hig: in_group = paren_prefix_in_group i l |- _ =>
        rewrite <- Hig, Hnth;
        unfold paren_step_in_group; simpl; reflexivity
      end.
    + lia.
    + dump_pre_spatial; lia.
    + lia.
    + dump_pre_spatial; lia.
    + lia.
    + lia.
    + (* output_acc_2 = paren_prefix_output (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_output_step by lia.
      match goal with
        Hout: output_acc_2 = paren_prefix_output i l,
        Hig: in_group = paren_prefix_in_group i l,
        Hmax: max_level = paren_prefix_max i l |- _ =>
        rewrite <- Hout, <- Hig, <- Hmax, Hnth;
        unfold paren_step_output; simpl; exact Hout
      end.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
Qed.

Lemma proof_of_p006_parse_nested_parens_entail_wit_2_4 : p006_parse_nested_parens_entail_wit_2_4.
Proof.
  pre_process.
  (* Premises: ch = 40 ('('), level+1 <= max_level *)
  assert (Hlen: i < Zlength l) by (match goal with H: Zlength l = len |- _ => rewrite H; assumption end).
  assert (Hnth: Znth i l 0 = 40).
  { pose proof (app_Znth1 l (0::nil) i ltac:(lia)). congruence. }
  Exists output_acc_2.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
    + (* level+1 = paren_prefix_level (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_level_step by lia.
      match goal with
        Hlev: level = paren_prefix_level i l,
        Hig: in_group = paren_prefix_in_group i l |- _ =>
        rewrite <- Hlev, <- Hig, Hnth;
        unfold paren_step_level; simpl; lia
      end.
    + (* max_level = paren_prefix_max (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_max_step by lia.
      match goal with
        Hlev: level = paren_prefix_level i l,
        Hig: in_group = paren_prefix_in_group i l,
        Hmax: max_level = paren_prefix_max i l,
        Hle: (level + 1) <= max_level |- _ =>
        rewrite <- Hlev, <- Hig, <- Hmax, Hnth;
        unfold paren_step_max; simpl;
        unfold paren_zmax;
        destruct (Z.leb_spec max_level (level + 1));
        [lia | exact Hmax]
      end.
    + (* 1 = paren_prefix_in_group (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_in_group_step by lia.
      match goal with Hig: in_group = paren_prefix_in_group i l |- _ =>
        rewrite <- Hig, Hnth;
        unfold paren_step_in_group; simpl; reflexivity
      end.
    + lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + lia.
    + lia.
    + (* output_acc_2 = paren_prefix_output (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_output_step by lia.
      match goal with
        Hout: output_acc_2 = paren_prefix_output i l,
        Hig: in_group = paren_prefix_in_group i l,
        Hmax: max_level = paren_prefix_max i l |- _ =>
        rewrite <- Hout, <- Hig, <- Hmax, Hnth;
        unfold paren_step_output; simpl; exact Hout
      end.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
Qed.

Lemma proof_of_p006_parse_nested_parens_entail_wit_2_5 : p006_parse_nested_parens_entail_wit_2_5.
Proof.
  pre_process.
  (* Premises: ch <> 40, ch <> 32, level > 0 *)
  assert (Hlen: i < Zlength l) by (match goal with H: Zlength l = len |- _ => rewrite H; assumption end).
  assert (Hnth_ne32: Znth i l 0 <> 32).
  { pose proof (app_Znth1 l (0::nil) i ltac:(lia)). congruence. }
  assert (Hnth_ne40: Znth i l 0 <> 40).
  { pose proof (app_Znth1 l (0::nil) i ltac:(lia)). congruence. }
  set (ch := Znth i l 0) in *.
  Exists output_acc_2.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
    + (* level-1 = paren_prefix_level (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_level_step by lia.
      match goal with
        Hlev: level = paren_prefix_level i l,
        Hig: in_group = paren_prefix_in_group i l,
        Hlvgt: level > 0 |- _ =>
        rewrite <- Hlev, <- Hig;
        unfold paren_step_level;
        assert (Z.eqb ch 32 = false) by (apply Z.eqb_neq; exact Hnth_ne32);
        assert (Z.eqb ch 40 = false) by (apply Z.eqb_neq; exact Hnth_ne40);
        rewrite H, H0;
        destruct (Z.ltb_spec 0 level);
        [lia | lia]
      end.
    + (* max_level = paren_prefix_max (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_max_step by lia.
      match goal with
        Hlev: level = paren_prefix_level i l,
        Hig: in_group = paren_prefix_in_group i l,
        Hmax: max_level = paren_prefix_max i l |- _ =>
        rewrite <- Hlev, <- Hig, <- Hmax;
        unfold paren_step_max;
        assert (Z.eqb ch 32 = false) by (apply Z.eqb_neq; exact Hnth_ne32);
        assert (Z.eqb ch 40 = false) by (apply Z.eqb_neq; exact Hnth_ne40);
        rewrite H, H0; exact Hmax
      end.
    + (* 1 = paren_prefix_in_group (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_in_group_step by lia.
      match goal with Hig: in_group = paren_prefix_in_group i l |- _ =>
        rewrite <- Hig;
        unfold paren_step_in_group;
        assert (Z.eqb ch 32 = false) by (apply Z.eqb_neq; exact Hnth_ne32);
        rewrite H; reflexivity
      end.
    + lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + lia.
    + lia.
    + (* output_acc_2 = paren_prefix_output (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_output_step by lia.
      match goal with
        Hout: output_acc_2 = paren_prefix_output i l,
        Hig: in_group = paren_prefix_in_group i l,
        Hmax: max_level = paren_prefix_max i l |- _ =>
        rewrite <- Hout, <- Hig, <- Hmax;
        unfold paren_step_output;
        assert (Z.eqb ch 32 = false) by (apply Z.eqb_neq; exact Hnth_ne32);
        rewrite H; exact Hout
      end.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
Qed.

Lemma proof_of_p006_parse_nested_parens_entail_wit_2_6 : p006_parse_nested_parens_entail_wit_2_6.
Proof.
  pre_process.
  (* Premises: ch <> 40, ch <> 32, level <= 0 (and 0 <= level, so level = 0) *)
  assert (Hlen: i < Zlength l) by (match goal with H: Zlength l = len |- _ => rewrite H; assumption end).
  assert (Hnth_ne32: Znth i l 0 <> 32).
  { pose proof (app_Znth1 l (0::nil) i ltac:(lia)). congruence. }
  assert (Hnth_ne40: Znth i l 0 <> 40).
  { pose proof (app_Znth1 l (0::nil) i ltac:(lia)). congruence. }
  set (ch := Znth i l 0) in *.
  Exists output_acc_2.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
    + (* level = paren_prefix_level (i+1) l -- level stays 0 *)
      dump_pre_spatial.
      rewrite paren_prefix_level_step by lia.
      match goal with
        Hlev: level = paren_prefix_level i l,
        Hig: in_group = paren_prefix_in_group i l,
        Hlvle: level <= 0,
        Hlvge: 0 <= level |- _ =>
        rewrite <- Hlev, <- Hig;
        unfold paren_step_level;
        assert (Z.eqb ch 32 = false) by (apply Z.eqb_neq; exact Hnth_ne32);
        assert (Z.eqb ch 40 = false) by (apply Z.eqb_neq; exact Hnth_ne40);
        rewrite H, H0;
        destruct (Z.ltb_spec 0 level);
        [lia | lia]
      end.
    + (* max_level = paren_prefix_max (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_max_step by lia.
      match goal with
        Hlev: level = paren_prefix_level i l,
        Hig: in_group = paren_prefix_in_group i l,
        Hmax: max_level = paren_prefix_max i l |- _ =>
        rewrite <- Hlev, <- Hig, <- Hmax;
        unfold paren_step_max;
        assert (Z.eqb ch 32 = false) by (apply Z.eqb_neq; exact Hnth_ne32);
        assert (Z.eqb ch 40 = false) by (apply Z.eqb_neq; exact Hnth_ne40);
        rewrite H, H0; exact Hmax
      end.
    + (* 1 = paren_prefix_in_group (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_in_group_step by lia.
      match goal with Hig: in_group = paren_prefix_in_group i l |- _ =>
        rewrite <- Hig;
        unfold paren_step_in_group;
        assert (Z.eqb ch 32 = false) by (apply Z.eqb_neq; exact Hnth_ne32);
        rewrite H; reflexivity
      end.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + lia.
    + lia.
    + (* output_acc_2 = paren_prefix_output (i+1) l *)
      dump_pre_spatial.
      rewrite paren_prefix_output_step by lia.
      match goal with
        Hout: output_acc_2 = paren_prefix_output i l,
        Hig: in_group = paren_prefix_in_group i l,
        Hmax: max_level = paren_prefix_max i l |- _ =>
        rewrite <- Hout, <- Hig, <- Hmax;
        unfold paren_step_output;
        assert (Z.eqb ch 32 = false) by (apply Z.eqb_neq; exact Hnth_ne32);
        rewrite H; exact Hout
      end.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
Qed.

Lemma proof_of_p006_parse_nested_parens_return_wit_1 : p006_parse_nested_parens_return_wit_1.
Proof.
  pre_process.
  (* in_group <> 0, writes max_level; i = len since i >= len and i <= len *)
  (* Existentials: data, output_l, output_size *)
  Exists data_2.
  Exists (app output_acc (cons max_level nil)).
  Exists (Zlength output_acc + 1).
  rewrite Zlength_app; simpl.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
    + lia.
    + lia.
    + (* Zlength output_acc + 1 <= len *)
      dump_pre_spatial.
      match goal with
        Hig: in_group <> 0,
        Hbound: 2 * Zlength output_acc + in_group <= i,
        Hile: i <= len,
        Hige: i >= len,
        Higge: 0 <= in_group,
        Higle: in_group <= 1 |- _ =>
        lia
      end.
    + (* problem_6_spec l (output_acc ++ [max_level]) *)
      dump_pre_spatial.
      unfold problem_6_spec.
      rewrite paren_output_eq.
      match goal with
        Hout: output_acc = paren_prefix_output i l,
        Hig: in_group = paren_prefix_in_group i l,
        Hmax: max_level = paren_prefix_max i l,
        Hige: i >= len,
        Hile: i <= len,
        Hzlen: Zlength l = len,
        Higne: in_group <> 0 |- _ =>
        assert (Hi: i = len) by lia;
        subst i;
        rewrite <- Hzlen;
        rewrite <- Hout, <- Hig, <- Hmax;
        unfold paren_final_output;
        assert (Z.eqb in_group 0 = false) by (apply Z.eqb_neq; exact Higne);
        rewrite H; reflexivity
      end.
Qed.

Lemma proof_of_p006_parse_nested_parens_return_wit_2 : p006_parse_nested_parens_return_wit_2.
Proof.
  pre_process.
  (* in_group = 0, no extra write *)
  Exists data_2.
  Exists output_acc.
  Exists (Zlength output_acc).
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
    + lia.
    + dump_pre_spatial; lia.
    + (* Zlength output_acc <= len *)
      dump_pre_spatial.
      match goal with
        Hig0: in_group = 0,
        Hbound: 2 * Zlength output_acc + in_group <= i,
        Hile: i <= len |- _ =>
        lia
      end.
    + (* problem_6_spec l output_acc *)
      dump_pre_spatial.
      unfold problem_6_spec.
      rewrite paren_output_eq.
      match goal with
        Hout: output_acc = paren_prefix_output i l,
        Hig: in_group = paren_prefix_in_group i l,
        Hmax: max_level = paren_prefix_max i l,
        Hige: i >= len,
        Hile: i <= len,
        Hzlen: Zlength l = len,
        Hig0: in_group = 0 |- _ =>
        assert (Hi: i = len) by lia;
        subst i;
        rewrite <- Hzlen;
        rewrite <- Hout, <- Hig, <- Hmax;
        unfold paren_final_output;
        rewrite Hig0; simpl; exact Hout
      end.
Qed.

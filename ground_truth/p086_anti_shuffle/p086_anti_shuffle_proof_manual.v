Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p086_anti_shuffle Require Import p086_anti_shuffle_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p086_anti_shuffle.
Local Open Scope sac.

Lemma proof_of_p086_anti_shuffle_entail_wit_1 : p086_anti_shuffle_entail_wit_1.
Proof.
  pre_process.
  subst retval.
  sep_apply (CharArray.undef_full_split_to_undef_seg retval_2 0 (len + 1)).
  2: lia.
  sep_apply (CharArray.undef_full_split_to_undef_seg retval_3 0 (len + 1)).
  2: lia.
  rewrite (CharArray.full_empty retval_2 0).
  rewrite (CharArray.full_empty retval_3 0).
  rewrite (CharArray.undef_seg_empty retval_2 0).
  rewrite (CharArray.undef_seg_empty retval_3 0).
  entailer!.
  all: try (intros k Hk;
    match goal with
    | H : forall k0 : Z, _ -> _ |- _ => eapply H; lia
    end).
  all: try solve [
    unfold anti_out_prefix, anti_cur_prefix; simpl;
    try rewrite Zlength_nil; lia
  ].
Qed. 

Lemma proof_of_p086_anti_shuffle_entail_wit_2_1 : p086_anti_shuffle_entail_wit_2_1.
Proof.
  pre_process.
  repeat match goal with
  | H : context[Znth i (app l (cons 0 nil)) 0] |- _ =>
      rewrite Znth_app_l_0_86 in H by lia
  end.
  rewrite Znth_app_l_0_86 by lia.
  match goal with
  | Hneq : Znth i l 0 <> 32 |- _ =>
      pose proof (anti_prefix_step_nonspace_86 i l ltac:(lia)
        (is_space_eq_false_86 _ Hneq)) as [Hout Hcur]
  end.
  rewrite Hout, Hcur.
  pose proof (anti_prefix_lengths i l ltac:(lia)) as Hprefix_len.
  match goal with
  | Houtlen : out_len = Zlength (anti_out_prefix i l),
    Hcurlen : cur_len = Zlength (anti_cur_prefix i l) |- _ =>
      rewrite <- Houtlen, <- Hcurlen in Hprefix_len
  end.
  entailer!.
  all: repeat rewrite Zlength_app; repeat rewrite Zlength_cons;
    repeat rewrite Zlength_nil; lia.
Qed. 

Lemma proof_of_p086_anti_shuffle_entail_wit_2_2 : p086_anti_shuffle_entail_wit_2_2.
Proof.
  pre_process.
  repeat match goal with
  | H : context[Znth i (app l (cons 0 nil)) 0] |- _ =>
      rewrite Znth_app_l_0_86 in H by lia
  end.
  match goal with
  | Hspace : Znth i l 0 = 32 |- _ =>
      pose proof (anti_prefix_step_space_86 i l ltac:(lia)
        (is_space_eq_true_86 _ Hspace)) as [Hout Hcur]
  end.
  rewrite Hout, Hcur.
  pose proof (anti_prefix_lengths i l ltac:(lia)) as Hprefix_len.
  match goal with
  | Houtlen : out_len = Zlength (anti_out_prefix i l),
    Hcurlen : cur_len = Zlength (anti_cur_prefix i l) |- _ =>
      rewrite <- Houtlen, <- Hcurlen in Hprefix_len
  end.
  rewrite (CharArray.full_empty cur 0).
  sep_apply (CharArray.full_to_undef_full cur cur_len (sort_chars (anti_cur_prefix i l))).
  sep_apply (CharArray.undef_full_to_undef_seg cur cur_len).
  sep_apply (CharArray.undef_seg_merge_to_undef_seg cur 0 cur_len cap); try lia.
  entailer!.
  - rewrite app_assoc.
    cancel.
  - repeat rewrite Zlength_app; repeat rewrite Zlength_cons;
    repeat rewrite Zlength_nil; rewrite ?Zlength_sort_chars; lia.
Qed. 

Lemma proof_of_p086_anti_shuffle_entail_wit_3 : p086_anti_shuffle_entail_wit_3.
Proof.
  pre_process.
  assert (i = len) by lia.
  subst i.
  pose proof (anti_prefix_lengths len l ltac:(lia)) as Hprefix_len.
  match goal with
  | Houtlen : out_len = Zlength (anti_out_prefix len l),
    Hcurlen : cur_len = Zlength (anti_cur_prefix len l) |- _ =>
      rewrite <- Houtlen, <- Hcurlen in Hprefix_len
  end.
  entailer!.
  - unfold anti_shuffle_output.
    match goal with
    | Hlen : Zlength l = len |- _ => rewrite Hlen
    end.
    cancel.
  - apply problem_86_spec_anti_shuffle_output_86.
    assumption.
  - rewrite anti_shuffle_output_length_86.
    lia.
Qed. 

Lemma proof_of_p086_anti_shuffle_return_wit_1 : p086_anti_shuffle_return_wit_1.
Proof.
  pre_process.
  Exists (anti_shuffle_output l).
  replace (out_len + 1) with cap by
    (rewrite H, H9, anti_shuffle_output_length_86, H4; lia).
  rewrite (CharArray.undef_seg_empty out cap).
  replace cap with (Zlength (anti_shuffle_output l) + 1) by
    (rewrite H, anti_shuffle_output_length_86, H4; lia).
  entailer!.
  intros k Hk.
  eapply anti_shuffle_output_Znth_nonzero_86; [| exact Hk].
  intros j Hj.
  apply H7.
  rewrite <- H4.
  exact Hj.
Qed. 

Lemma proof_of_p086_anti_shuffle_partial_solve_wit_8_pure : p086_anti_shuffle_partial_solve_wit_8_pure.
Proof.
  pre_process.
  entailer!.
  rewrite Zlength_sort_chars.
  lia.
Qed. 

Lemma proof_of_p086_anti_shuffle_partial_solve_wit_10_pure : p086_anti_shuffle_partial_solve_wit_10_pure.
Proof.
  pre_process.
  assert (i = len) by lia.
  subst i.
  entailer!.
Qed.

Lemma proof_of_p086_anti_shuffle_partial_solve_wit_11_pure : p086_anti_shuffle_partial_solve_wit_11_pure.
Proof.
  pre_process.
  assert (i = len) by lia.
  subst i.
  entailer!.
  all: try rewrite Zlength_sort_chars; lia.
Qed. 

Lemma proof_of_p086_anti_shuffle_partial_solve_wit_12_pure : p086_anti_shuffle_partial_solve_wit_12_pure.
Proof.
  pre_process.
  assert (i = len) by lia.
  subst i.
  entailer!.
  rewrite Zlength_sort_chars.
  lia.
Qed. 

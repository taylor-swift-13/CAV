Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p103_rounded_avg Require Import p103_rounded_avg_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p103_rounded_avg.
Require Import base_conversion_lib.
Local Open Scope sac.

Lemma proof_of_p103_rounded_avg_safety_wit_24 : p103_rounded_avg_safety_wit_24.
Proof.
  unfold p103_rounded_avg_safety_wit_24.
  intros.
  pre_process.
  assert (total <= num) by
    (subst total; apply binary_digits_length_pos_le; lia).
  entailer!.
Qed. 

Lemma proof_of_p103_rounded_avg_safety_wit_28 : p103_rounded_avg_safety_wit_28.
Proof.
  unfold p103_rounded_avg_safety_wit_28.
  intros.
  pre_process.
  pose proof (Z.rem_bound_pos num 2 ltac:(lia) ltac:(lia)).
  entailer!.
Qed. 

Lemma proof_of_p103_rounded_avg_entail_wit_1 : p103_rounded_avg_entail_wit_1.
Proof.
  unfold p103_rounded_avg_entail_wit_1.
  intros.
  pre_process.
  replace ((n_pre + m_pre) ÷ 2) with ((n_pre + m_pre) / 2)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  entailer!.
  - apply binary_count_state_init.
    unfold avg_103. apply Z.div_str_pos; lia.
  - unfold avg_103. apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
  - apply Z.div_str_pos; lia.
Qed. 

Lemma proof_of_p103_rounded_avg_entail_wit_2 : p103_rounded_avg_entail_wit_2.
Proof.
  unfold p103_rounded_avg_entail_wit_2.
  intros.
  pre_process.
  replace (t ÷ 2) with (t / 2)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  entailer!.
  - apply binary_count_state_step; lia || assumption.
  - apply binary_count_state_step_safe with (orig := num) (t := t); lia || assumption.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_p103_rounded_avg_entail_wit_3 : p103_rounded_avg_entail_wit_3.
Proof.
  unfold p103_rounded_avg_entail_wit_3.
  intros.
  pre_process.
  assert (t = 0) by lia; subst t.
  rewrite (CharArray.full_empty retval 0).
  entailer!.
  - unfold CharArray.undef_full, CharArray.undef_seg.
    unfold store_undef_array.
    replace (digits + 1 - 0) with (digits + 1) by lia.
    entailer!.
  - apply binary_count_state_done; lia || assumption.
Qed. 

Lemma proof_of_p103_rounded_avg_entail_wit_4 : p103_rounded_avg_entail_wit_4.
Proof.
  unfold p103_rounded_avg_entail_wit_4.
  intros.
  pre_process.
  rewrite repeat_Z_tail by lia.
  entailer!.
Qed. 

Lemma proof_of_p103_rounded_avg_entail_wit_5 : p103_rounded_avg_entail_wit_5.
Proof.
  unfold p103_rounded_avg_entail_wit_5.
  intros.
  pre_process.
  assert (i = total + 1) by lia; subst i.
  rewrite (CharArray.undef_seg_empty out (total + 1)).
  Exists (repeat_Z 0 total).
  entailer!.
  - rewrite naive_C_Rules.repeat_Z_tail
      by (pose proof (Zlength_nonneg (binary_digits num)); lia).
    unfold naive_C_Rules.repeat_Z, repeat_Z.
    entailer!.
  - subst digits. subst total. apply binary_fill_full_state_init; lia.
  - rewrite Zlength_repeat_Z by
      (pose proof (Zlength_nonneg (binary_digits num)); lia).
    lia.
Qed. 

Lemma proof_of_p103_rounded_avg_entail_wit_6 : p103_rounded_avg_entail_wit_6.
Proof.
  unfold p103_rounded_avg_entail_wit_6.
  intros.
  pre_process.
  subst orig.
  Exists out_l_2.
  entailer!.
  pose proof (Zlength_nonneg (binary_digits num)).
  lia.
Qed. 

Lemma proof_of_p103_rounded_avg_entail_wit_7 : p103_rounded_avg_entail_wit_7.
Proof.
  unfold p103_rounded_avg_entail_wit_7.
  intros.
  pre_process.
  Exists out_l_2.
  entailer!.
  - replace (digits - 1 + 1) with digits by lia.
    assumption.
  - pose proof (base_fill_full_state_positive_digits orig 2 num digits out_l_2
      ltac:(lia) ltac:(lia) H14).
    lia.
Qed. 

Lemma proof_of_p103_rounded_avg_entail_wit_8 : p103_rounded_avg_entail_wit_8.
Proof.
  unfold p103_rounded_avg_entail_wit_8.
  intros.
  pre_process.
  replace (num ÷ 2) with (num / 2)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  replace (Z.rem num 2) with (num mod 2)
    by (symmetry; apply Z.rem_mod_nonneg; lia).
  Exists (replace_Znth digits (signed_last_nbits (48 + num mod 2) 8) out_l_2).
  rewrite replace_Znth_app_l by lia.
  entailer!.
  - apply binary_fill_full_state_step; lia || assumption.
  - rewrite Zlength_replace_Znth_44 by lia. lia.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_p103_rounded_avg_return_wit_1 : p103_rounded_avg_return_wit_1.
Proof.
  unfold p103_rounded_avg_return_wit_1.
  intros.
  pre_process.
  assert (num = 0) by lia; subst num.
  unfold binary_fill_full_state in H14.
  destruct H14 as [suffix [[_ [_ [Hdigits Hsplit]]] Hout]].
  unfold base_digits_pos in Hdigits.
  replace (Z.leb 0 0) with true in Hdigits by (symmetry; apply Z.leb_le; lia).
  simpl in Hdigits. subst digits.
  simpl in Hsplit. subst suffix.
  unfold repeat_Z in Hout. simpl in Hout. subst out_l_2.
  Exists (binary_digits orig) (Zlength (binary_digits orig)).
  replace (Zlength (binary_digits orig) + 1) with (total + 1) by lia.
  entailer!.
  - apply problem_103_spec_binary; try lia.
    match goal with
    | H: orig = avg_103 n_pre m_pre |- _ => rewrite H; reflexivity
    end.
  - pose proof (binary_digits_length_pos_le orig ltac:(lia)).
    lia.
  - pose proof (binary_digits_nonempty orig) as Hnonempty.
    destruct (binary_digits orig) eqn:Hbd; [contradiction | idtac].
    rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia.
  - intros k Hk.
    apply binary_digits_nonzero; lia.
Qed. 

Lemma proof_of_p103_rounded_avg_return_wit_2 : p103_rounded_avg_return_wit_2.
Proof.
  unfold p103_rounded_avg_return_wit_2.
  intros.
  pre_process.
  Exists ((45 :: 49 :: nil) : list Z) 2.
  rewrite (CharArray.undef_seg_empty retval 3).
  entailer!.
  - change (List.app (45 :: 49 :: nil) (0 :: nil)) with (45 :: 49 :: 0 :: nil).
    rewrite (CharArray.full_unfold retval (2 + 1) (49 :: 0 :: nil) 45).
    rewrite (CharArray.seg_unfold retval 1 (2 + 1) (0 :: nil) 49).
    rewrite (CharArray.seg_unfold retval 2 (2 + 1) nil 0).
    rewrite (CharArray.seg_empty retval 3 3).
    entailer!.
  - apply problem_103_spec_neg; lia.
  - intros k Hk.
    assert (Hcase : k = 0 \/ k = 1) by lia.
    destruct Hcase as [-> | ->]; unfold Znth; simpl; lia.
Qed. 

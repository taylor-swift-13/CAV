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
From SimpleC.EE Require Import p156_int_to_mini_romank_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Strings.Ascii.

Import naive_C_Rules.
Require Import p156_int_to_mini_romank.
Local Open Scope sac.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
Require Import string_bridge.

Local Open Scope list_scope.

(* Proof helpers moved from p156_int_to_mini_romank.v so public contract files expose definitions only. *)

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


Lemma proof_of_append_roman_digit_return_wit_1 : append_roman_digit_return_wit_1.
Proof.
  unfold append_roman_digit_return_wit_1.
  intros. pre_process.
  assert (digit_pre = 9) by lia; subst digit_pre.
  Exists (one_pre :: ten_pre :: nil).
  entailer!.
  replace (pos_pre + 1 + 1) with (pos_pre + 2) by lia.
  rewrite <- app_assoc. simpl.
  entailer!.
Qed. 

Lemma proof_of_append_roman_digit_return_wit_2 : append_roman_digit_return_wit_2.
Proof.
  unfold append_roman_digit_return_wit_2.
  intros. pre_process. subst digit_pre.
  Exists (five_pre :: one_pre :: one_pre :: one_pre :: nil).
  entailer!.
  replace (((pos_pre + 1 + 1 + 1) + 1)) with (pos_pre + 4) by lia.
  replace (pos_pre + 3 + 1) with (pos_pre + 4) by lia.
  repeat rewrite <- app_assoc. simpl.
  entailer!.
Qed. 

Lemma proof_of_append_roman_digit_return_wit_3 : append_roman_digit_return_wit_3.
Proof.
  unfold append_roman_digit_return_wit_3.
  intros. pre_process. subst digit_pre.
  Exists (five_pre :: one_pre :: one_pre :: nil).
  entailer!.
  replace (pos_pre + 1 + 1 + 1) with (pos_pre + 3) by lia.
  replace (pos_pre + 2 + 1) with (pos_pre + 3) by lia.
  repeat rewrite <- app_assoc. simpl.
  entailer!.
Qed. 

Lemma proof_of_append_roman_digit_return_wit_4 : append_roman_digit_return_wit_4.
Proof.
  unfold append_roman_digit_return_wit_4.
  intros. pre_process. subst digit_pre.
  Exists (five_pre :: one_pre :: nil).
  entailer!.
  replace (pos_pre + 1 + 1) with (pos_pre + 2) by lia.
  rewrite <- app_assoc. simpl.
  entailer!.
Qed. 

Lemma proof_of_append_roman_digit_return_wit_5 : append_roman_digit_return_wit_5.
Proof.
  unfold append_roman_digit_return_wit_5.
  intros. pre_process. subst digit_pre.
  Exists (five_pre :: nil).
  entailer!.
Qed. 

Lemma proof_of_append_roman_digit_return_wit_6 : append_roman_digit_return_wit_6.
Proof.
  unfold append_roman_digit_return_wit_6.
  intros. pre_process. subst digit_pre.
  Exists (one_pre :: five_pre :: nil).
  entailer!.
  replace (pos_pre + 1 + 1) with (pos_pre + 2) by lia.
  rewrite <- app_assoc. simpl.
  entailer!.
Qed. 

Lemma proof_of_append_roman_digit_return_wit_7 : append_roman_digit_return_wit_7.
Proof.
  unfold append_roman_digit_return_wit_7.
  intros. pre_process. subst digit_pre.
  Exists (one_pre :: one_pre :: one_pre :: nil).
  entailer!.
  replace (pos_pre + 1 + 1 + 1) with (pos_pre + 3) by lia.
  replace (pos_pre + 2 + 1) with (pos_pre + 3) by lia.
  repeat rewrite <- app_assoc. simpl.
  entailer!.
Qed. 

Lemma proof_of_append_roman_digit_return_wit_8 : append_roman_digit_return_wit_8.
Proof.
  unfold append_roman_digit_return_wit_8.
  intros. pre_process. subst digit_pre.
  Exists (one_pre :: one_pre :: nil).
  entailer!.
  replace (pos_pre + 1 + 1) with (pos_pre + 2) by lia.
  rewrite <- app_assoc. simpl.
  entailer!.
Qed. 

Lemma proof_of_append_roman_digit_return_wit_9 : append_roman_digit_return_wit_9.
Proof.
  unfold append_roman_digit_return_wit_9.
  intros. pre_process. subst digit_pre.
  Exists (one_pre :: nil).
  entailer!.
Qed. 

Lemma proof_of_append_roman_digit_return_wit_10 : append_roman_digit_return_wit_10.
Proof.
  unfold append_roman_digit_return_wit_10.
  intros. pre_process. subst digit_pre.
  Exists (@nil Z).
  rewrite app_nil_r.
  entailer!.
  cbn; lia.
Qed. 

Lemma proof_of_p156_int_to_mini_romank_entail_wit_1_1 : p156_int_to_mini_romank_entail_wit_1_1.
Proof.
  unfold p156_int_to_mini_romank_entail_wit_1_1.
  intros. pre_process. subst number_pre.
  unfold roman_thousand, roman_thousand_list.
  rewrite Z.eqb_refl.
  entailer!.
  rewrite (CharArray.full_unfold retval 1 nil 109).
  replace (0 + 1) with 1 by lia.
  rewrite (CharArray.seg_empty retval 1 1).
  entailer!.
Qed. 

Lemma proof_of_p156_int_to_mini_romank_entail_wit_1_2 : p156_int_to_mini_romank_entail_wit_1_2.
Proof.
  unfold p156_int_to_mini_romank_entail_wit_1_2.
  intros. pre_process.
  unfold roman_thousand, roman_thousand_list.
  destruct (Z.eqb number_pre 1000) eqn:Hthousand.
  { apply Z.eqb_eq in Hthousand; lia. }
  rewrite (CharArray.full_empty retval 0).
  unfold CharArray.undef_full, CharArray.undef_seg, store_undef_array.
  replace (64 - 0) with 64 by lia.
  entailer!.
Qed. 

Lemma proof_of_p156_int_to_mini_romank_entail_wit_2 : p156_int_to_mini_romank_entail_wit_2.
Proof.
  unfold p156_int_to_mini_romank_entail_wit_2.
  intros. pre_process.
  subst number.
  replace (number_pre ÷ 100) with (number_pre / 100) in H
    by (symmetry; apply Z.quot_div_nonneg; lia).
  replace ((number_pre / 100) % 10) with ((number_pre / 100) mod 10) in H
    by (symmetry; apply Z.rem_mod_nonneg; try apply Z.div_pos; lia).
  pose proof (roman_prefix1_step number_pre chunk ltac:(lia) H) as Hstep.
  unfold roman_prefix1.
  rewrite Hstep.
  entailer!.
  rewrite Zlength_app.
  unfold roman_digit in H; subst chunk.
  lia.
Qed. 

Lemma proof_of_p156_int_to_mini_romank_entail_wit_3 : p156_int_to_mini_romank_entail_wit_3.
Proof.
  unfold p156_int_to_mini_romank_entail_wit_3.
  intros. pre_process.
  subst number.
  replace (number_pre ÷ 10) with (number_pre / 10) in H
    by (symmetry; apply Z.quot_div_nonneg; lia).
  replace ((number_pre / 10) % 10) with ((number_pre / 10) mod 10) in H
    by (symmetry; apply Z.rem_mod_nonneg; try apply Z.div_pos; lia).
  pose proof (roman_prefix2_step number_pre chunk ltac:(lia) H) as Hstep.
  unfold roman_prefix2.
  rewrite Hstep.
  entailer!.
  rewrite Zlength_app.
  unfold roman_digit in H; subst chunk.
  lia.
Qed. 

Lemma proof_of_p156_int_to_mini_romank_entail_wit_4 : p156_int_to_mini_romank_entail_wit_4.
Proof.
  unfold p156_int_to_mini_romank_entail_wit_4.
  intros. pre_process.
  subst number.
  replace (number_pre % 10) with (number_pre mod 10) in H
    by (symmetry; apply Z.rem_mod_nonneg; lia).
  pose proof (roman_output_step number_pre chunk H) as Hstep.
  unfold roman_output.
  rewrite Hstep.
  entailer!.
  - rewrite Zlength_app.
    lia.
  - pose proof (roman_output_length_bound number_pre
      (roman_output_list number_pre) ltac:(lia) ltac:(reflexivity)) as Hlen.
    rewrite Hstep in Hlen.
    rewrite Zlength_app in Hlen.
    unfold roman_digit in H; subst chunk.
    lia.
Qed. 

Lemma proof_of_p156_int_to_mini_romank_return_wit_1 : p156_int_to_mini_romank_return_wit_1.
Proof.
  unfold p156_int_to_mini_romank_return_wit_1.
  intros. pre_process.
  Exists (roman_output_list number_pre) k_2.
  entailer!.
  - apply problem_156_spec_intro; try lia.
    assumption.
  - intros p Hp.
    apply roman_output_list_Znth_nonzero; lia.
Qed. 

Lemma proof_of_p156_int_to_mini_romank_partial_solve_wit_3_pure : p156_int_to_mini_romank_partial_solve_wit_3_pure.
Proof.
  unfold p156_int_to_mini_romank_partial_solve_wit_3_pure.
  intros. pre_process.
  subst number.
  replace ((number_pre ÷ 100) % 10) with ((number_pre / 100) mod 10)
    by (replace (number_pre ÷ 100) with (number_pre / 100)
          by (symmetry; apply Z.quot_div_nonneg; lia);
        symmetry; apply Z.rem_mod_nonneg; try apply Z.div_pos; lia).
  pose proof (roman_thousand_length_bound number_pre
    (roman_thousand_list number_pre) ltac:(lia) H6).
  pose proof (Z.mod_pos_bound (number_pre / 100) 10 ltac:(lia)).
  entailer!; try lia.
Qed. 

Lemma proof_of_p156_int_to_mini_romank_partial_solve_wit_4_pure : p156_int_to_mini_romank_partial_solve_wit_4_pure.
Proof.
  unfold p156_int_to_mini_romank_partial_solve_wit_4_pure.
  intros. pre_process.
  subst number.
  replace ((number_pre ÷ 10) % 10) with ((number_pre / 10) mod 10)
    by (replace (number_pre ÷ 10) with (number_pre / 10)
          by (symmetry; apply Z.quot_div_nonneg; lia);
        symmetry; apply Z.rem_mod_nonneg; try apply Z.div_pos; lia).
  pose proof (roman_prefix1_length_bound number_pre
    (roman_prefix1_list number_pre) ltac:(lia) H6).
  pose proof (Z.mod_pos_bound (number_pre / 10) 10 ltac:(lia)).
  entailer!; try lia.
Qed. 

Lemma proof_of_p156_int_to_mini_romank_partial_solve_wit_5_pure : p156_int_to_mini_romank_partial_solve_wit_5_pure.
Proof.
  unfold p156_int_to_mini_romank_partial_solve_wit_5_pure.
  intros. pre_process.
  subst number.
  replace (number_pre % 10) with (number_pre mod 10)
    by (symmetry; apply Z.rem_mod_nonneg; lia).
  pose proof (roman_prefix2_length_bound number_pre
    (roman_prefix2_list number_pre) ltac:(lia) H6).
  pose proof (Z.mod_pos_bound number_pre 10 ltac:(lia)).
  entailer!; try lia.
Qed. 

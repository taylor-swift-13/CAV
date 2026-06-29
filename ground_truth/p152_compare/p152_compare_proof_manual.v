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
From SimpleC.EE Require Import p152_compare_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Lia.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p152_compare.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p152_compare.v so public contract files expose definitions only. *)

Lemma compare_list_length : forall game guess,
  length game = length guess ->
  length (compare_list game guess) = length game.
Proof.
  induction game as [|g gs IH]; intros guess Hlen.
  - reflexivity.
  - destruct guess as [|q qs]; simpl in *; [lia|].
    f_equal.
    apply IH.
    lia.
Qed.
Lemma compare_prefix_0 : forall game guess,
  0 <= Zlength game ->
  0 <= Zlength guess ->
  compare_prefix 0 game guess nil.
Proof.
  intros.
  unfold compare_prefix, compare_prefix_list.
  rewrite !Zsublist_nil by lia.
  repeat split; try lia; reflexivity.
Qed.
Lemma compare_prefix_Zlength : forall i game guess output,
  compare_prefix i game guess output ->
  problem_152_pre game guess ->
  Zlength output = i.
Proof.
  intros i game guess output [Hbounds [Hguess Hout]] Hpre.
  subst output.
  unfold compare_prefix_list.
  unfold problem_152_pre, problem_152_pre in Hpre.
  rewrite Zlength_correct.
  rewrite compare_list_length.
  - assert (Hsub : length (sublist 0 i game) = Z.to_nat i).
    {
      rewrite sublist_length.
      - replace (i - 0) with i by lia. reflexivity.
      - lia.
      - destruct Hbounds as [_ Hile].
        exact Hile.
    }
    rewrite Hsub.
    rewrite Z2Nat.id by lia.
    reflexivity.
  - assert (Hg : length (sublist 0 i game) = Z.to_nat i).
    {
      rewrite sublist_length.
      - replace (i - 0) with i by lia. reflexivity.
      - lia.
      - destruct Hbounds as [_ Hile].
        exact Hile.
    }
    assert (Hq : length (sublist 0 i guess) = Z.to_nat i).
    {
      rewrite sublist_length.
      - replace (i - 0) with i by lia. reflexivity.
      - lia.
      - exact Hguess.
    }
    rewrite Hg, Hq.
    reflexivity.
Qed.
Lemma compare_prefix_snoc : forall i game guess output diff value,
  compare_prefix i game guess output ->
  0 <= i < Zlength game ->
  i < Zlength guess ->
  diff = Znth i game 0 - Znth i guess 0 ->
  value = Z.abs diff ->
  compare_prefix (i + 1) game guess (output ++ [value]).
Proof.
  intros i game guess output diff value [Hbounds [Hguess Hout]] Hi Higuess Hdiff Hvalue.
  subst output diff value.
  unfold compare_prefix, compare_prefix_list in *.
  repeat split; try lia.
  rewrite (sublist_split 0 (i + 1) i game)
    by lia.
  rewrite (sublist_split 0 (i + 1) i guess)
    by lia.
  rewrite (sublist_single 0 i game) by lia.
  rewrite (sublist_single 0 i guess) by lia.
  clear Hbounds Hguess.
  remember (sublist 0 i game) as gs.
  remember (sublist 0 i guess) as qs.
  assert (Hlen : length gs = length qs).
  {
    subst gs qs.
    assert (Hg : length (sublist 0 i game) = Z.to_nat i).
    {
      rewrite sublist_length.
      - replace (i - 0) with i by lia. reflexivity.
      - lia.
      - lia.
    }
    assert (Hq : length (sublist 0 i guess) = Z.to_nat i).
    {
      rewrite sublist_length.
      - replace (i - 0) with i by lia. reflexivity.
      - lia.
      - lia.
    }
    rewrite Hg, Hq.
    reflexivity.
  }
  clear Heqgs Heqqs.
  revert qs Hlen.
  induction gs as [|g gs IH]; intros qs Hlen; destruct qs as [|q qs]; simpl in *; try lia.
  - reflexivity.
  - f_equal.
    apply IH.
    lia.
Qed.
Lemma compare_prefix_snoc_Zlength : forall i game guess output diff value,
  compare_prefix i game guess output ->
  problem_152_pre game guess ->
  0 <= i < Zlength game ->
  diff = Znth i game 0 - Znth i guess 0 ->
  value = Z.abs diff ->
  Zlength (output ++ [value]) = i + 1.
Proof.
  intros.
  rewrite Zlength_app.
  rewrite (compare_prefix_Zlength i game guess output); try assumption.
  change (Zlength [value]) with 1.
  lia.
Qed.
Lemma compare_list_Znth : forall game guess i,
  Zlength game = Zlength guess ->
  0 <= i < Zlength game ->
  Znth i (compare_list game guess) 0 =
    Z.abs (Znth i game 0 - Znth i guess 0).
Proof.
  induction game as [|g gs IH]; intros guess i Hlen Hi.
  - rewrite Zlength_correct in Hi; simpl in Hi; lia.
  - destruct guess as [|q qs].
    + rewrite !Zlength_correct in Hlen; simpl in Hlen; lia.
    + destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
      * subst i.
        simpl compare_list.
        repeat rewrite Znth0_cons.
        reflexivity.
      * assert (0 < i) by lia.
        simpl compare_list.
        rewrite !Znth_cons by lia.
        apply IH.
        -- rewrite !Zlength_cons in Hlen; lia.
        -- rewrite Zlength_cons in Hi; lia.
Qed.
Lemma compare_int_range_at : forall game guess i,
  compare_int_range game guess ->
  0 <= i < Zlength game ->
  INT_MIN < Znth i game 0 - Znth i guess 0 <= INT_MAX.
Proof.
  intros.
  apply H; assumption.
Qed.
Lemma compare_prefix_full_spec : forall game guess output,
  compare_prefix (Zlength game) game guess output ->
  problem_152_pre game guess ->
  problem_152_spec game guess output.
Proof.
  intros game guess output Hpref Hpre.
  unfold problem_152_spec, problem_152_spec.
  unfold problem_152_pre, problem_152_pre in Hpre.
  split; [assumption|].
  split.
  - rewrite (compare_prefix_Zlength (Zlength game) game guess output); try assumption.
    reflexivity.
  - intros n Hn.
    destruct Hpref as [_ [_ Hout]].
    subst output.
    unfold compare_prefix_list.
    rewrite sublist_self by reflexivity.
    rewrite (sublist_self guess) by exact Hpre.
    apply compare_list_Znth; assumption.
Qed.


Lemma proof_of_abs_return_wit_1 : abs_return_wit_1.
Proof.
  pre_process.
Qed. 

Lemma proof_of_abs_return_wit_2 : abs_return_wit_2.
Proof.
  pre_process.
Qed. 

Lemma proof_of_p152_compare_safety_wit_5 : p152_compare_safety_wit_5.
Proof.
  pre_process.
  pose proof (compare_int_range_at game_l guess_l i H12 ltac:(lia)) as Hrange.
  entailer!.
Qed. 

Lemma proof_of_p152_compare_entail_wit_1 : p152_compare_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z).
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
  apply compare_prefix_0; lia.
Qed. 

Lemma proof_of_p152_compare_entail_wit_2 : p152_compare_entail_wit_2.
Proof.
  pre_process.
  Exists (output_l_2 ++ (retval :: nil)).
  entailer!.
  - eapply compare_prefix_snoc; eauto; try lia.
  - symmetry.
    eapply compare_prefix_snoc_Zlength; eauto; try lia.
Qed. 

Lemma proof_of_p152_compare_return_wit_1 : p152_compare_return_wit_1.
Proof.
  pre_process.
  replace i with n in * by lia.
  replace n with game_size_pre in * by lia.
  Exists output_l_2 game_size_pre data_2.
  rewrite (IntArray.undef_seg_empty data_2 game_size_pre).
  sep_apply (IntArray.seg_to_full data_2 0 game_size_pre).
  replace (data_2 + 0 * sizeof(INT)) with data_2 by lia.
  replace (game_size_pre - 0) with game_size_pre by lia.
  entailer!.
  apply compare_prefix_full_spec.
  - rewrite <- H8.
    assumption.
  - assumption.
Qed. 

Lemma proof_of_p152_compare_partial_solve_wit_5_pure : p152_compare_partial_solve_wit_5_pure.
Proof.
  pre_process.
  pose proof (compare_int_range_at game_l guess_l i H12 ltac:(lia)) as Hrange.
  entailer!.
Qed. 

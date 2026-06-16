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
From SimpleC.EE.CAV.verify_20260607_101652_p142_sum_squares Require Import p142_sum_squares_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p142_sum_squares.
Local Open Scope sac.

Lemma transformed_sum_from_app : forall l1 l2 start,
  transformed_sum_from (l1 ++ l2) start =
  transformed_sum_from l1 start + transformed_sum_from l2 (start + Zlength l1).
Proof.
  intros l1 l2 start.
  revert start.
  induction l1 as [|x xs IH].
  - intros. simpl. rewrite Zlength_nil. rewrite Z.add_0_r. reflexivity.
  - intros. replace ((x :: xs) ++ l2) with (x :: (xs ++ l2)) by reflexivity.
    cbn [transformed_sum_from].
    rewrite Zlength_cons.
    replace (start + Z.succ (Zlength xs)) with ((start + 1) + Zlength xs) by (rewrite Z.add_succ_r; lia).
    assert (Hstep : transformed_value start x + transformed_sum_from (xs ++ l2) (start + 1) =
                    transformed_value start x + transformed_sum_from xs (start + 1) + transformed_sum_from l2 ((start + 1) + Zlength xs)).
    { rewrite (IH (start + 1)). rewrite Z.add_assoc. reflexivity. }
    rewrite Hstep.
    reflexivity.
Qed.

Lemma transformed_prefix_sum_step : forall i l,
  0 <= i < Zlength l ->
  transformed_prefix_sum (i + 1) l = transformed_prefix_sum i l + transformed_value i (Znth i l 0).
Proof.
  intros i l Hi.
  unfold transformed_prefix_sum.
  assert (Hsplit : sublist 0 (i + 1) l = sublist 0 i l ++ sublist i (i + 1) l).
  { apply sublist_split; lia. }
  rewrite Hsplit.
  rewrite transformed_sum_from_app.
  assert (Hsingle : sublist i (i + 1) l = Znth i l 0 :: nil).
  { apply sublist_single; lia. }
  rewrite Hsingle.
  simpl.
  rewrite Zlength_sublist by lia.
  replace (i - 0) with i by lia.
  rewrite Z.add_0_r.
  reflexivity.
Qed.

Lemma proof_of_p142_sum_squares_safety_wit_6 : p142_sum_squares_safety_wit_6.
Proof.
  pre_process.
  unfold sum_squares_int_range in H6.
  destruct H6 as [Hrange _].
  assert (Hbound : INT_MIN <= sum + Znth i input_l 0 * Znth i input_l 0 <= INT_MAX).
  {
    assert (Hconj := Hrange i H7 H1).
    destruct Hconj as [Hsq [Hcube Hsum]].
    rewrite <- H9 in Hsum.
    assert (Htv : transformed_value i (Znth i input_l 0) = Znth i input_l 0 * Znth i input_l 0).
    { unfold transformed_value. rewrite Z.rem_mod_nonneg by lia. replace (i mod 3) with 0 by (rewrite Zmod_eq in H8; lia). reflexivity. }
    rewrite Htv in Hsum.
    exact Hsum.
  }
  split_pures.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_p142_sum_squares_safety_wit_7 : p142_sum_squares_safety_wit_7.
Proof.
  pre_process.
  unfold sum_squares_int_range in H6.
  destruct H6 as [Hrange _].
  assert (Hbound : INT_MIN <= Znth i input_l 0 * Znth i input_l 0 <= INT_MAX).
  {
    assert (Hconj := Hrange i H7 H1).
    destruct Hconj as [Hsq _].
    exact Hsq.
  }
  split_pures.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_p142_sum_squares_safety_wit_11 : p142_sum_squares_safety_wit_11.
Proof.
  pre_process.
  unfold sum_squares_int_range in H6.
  destruct H6 as [Hrange _].
  assert (Hbound : INT_MIN <= sum + (Znth i input_l 0 * Znth i input_l 0) * Znth i input_l 0 <= INT_MAX).
  {
    assert (Hconj := Hrange i H7 H1).
    destruct Hconj as [Hsq [Hcube Hsum]].
    rewrite <- H9 in Hsum.
    assert (Htv : transformed_value i (Znth i input_l 0) = (Znth i input_l 0 * Znth i input_l 0) * Znth i input_l 0).
    { unfold transformed_value. rewrite Z.rem_mod_nonneg by lia. 
      assert (Hmod3 : i mod 3 <> 0).
      { intro Hc. rewrite Hc in H8. inversion H8. }
      assert (Hmod4 : i mod 4 = 0).
      { apply Zmod_divides in H10. destruct H10 as [k Hk]. rewrite Hk. replace (4 * k) with (k * 4) by lia. rewrite Z.mul_mod_distr_l by lia. simpl. lia. }
      rewrite Hmod3. rewrite Hmod4. reflexivity. }
    rewrite Htv in Hsum.
    exact Hsum.
  }
  split_pures.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_p142_sum_squares_safety_wit_12 : p142_sum_squares_safety_wit_12.
Proof.
  pre_process.
  unfold sum_squares_int_range in H6.
  destruct H6 as [Hrange _].
  assert (Hbound : INT_MIN <= (Znth i input_l 0 * Znth i input_l 0) * Znth i input_l 0 <= INT_MAX).
  {
    assert (Hconj := Hrange i H7 H1).
    destruct Hconj as [_ [Hcube _]].
    exact Hcube.
  }
  split_pures.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_p142_sum_squares_safety_wit_13 : p142_sum_squares_safety_wit_13.
Proof.
  pre_process.
  unfold sum_squares_int_range in H6.
  destruct H6 as [Hrange _].
  assert (Hbound : INT_MIN <= Znth i input_l 0 * Znth i input_l 0 <= INT_MAX).
  {
    assert (Hconj := Hrange i H7 H1).
    destruct Hconj as [Hsq _].
    exact Hsq.
  }
  split_pures.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_p142_sum_squares_safety_wit_17 : p142_sum_squares_safety_wit_17.
Proof.
  pre_process.
  unfold sum_squares_int_range in H6.
  destruct H6 as [Hrange _].
  assert (Hbound : INT_MIN <= sum + Znth i input_l 0 <= INT_MAX).
  {
    assert (Hconj := Hrange i H7 H1).
    destruct Hconj as [Hsq [Hcube Hsum]].
    rewrite <- H9 in Hsum.
    assert (Htv : transformed_value i (Znth i input_l 0) = Znth i input_l 0).
    { unfold transformed_value. rewrite Z.rem_mod_nonneg by lia. 
      assert (Hmod3 : i mod 3 <> 0).
      { intro Hc. rewrite Hc in H8. inversion H8. }
      assert (Hmod4 : i mod 4 <> 0).
      { intro Hc. rewrite Hc in H10. inversion H10. }
      rewrite Hmod3. rewrite Hmod4. reflexivity. }
    rewrite Htv in Hsum.
    exact Hsum.
  }
  split_pures.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_p142_sum_squares_entail_wit_1 : p142_sum_squares_entail_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full lst_pre lst_size_pre input_l).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      unfold transformed_prefix_sum.
      simpl.
      reflexivity.
    + dump_pre_spatial. cancel (IntArray.full lst_pre lst_size_pre input_l).
Qed.

Lemma proof_of_p142_sum_squares_entail_wit_2_1 : p142_sum_squares_entail_wit_2_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full lst lst_size input_l).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      rewrite H9.
      apply transformed_prefix_sum_step.
      lia.
    + dump_pre_spatial. cancel (IntArray.full lst lst_size input_l).
Qed.

Lemma proof_of_p142_sum_squares_entail_wit_2_2 : p142_sum_squares_entail_wit_2_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full lst lst_size input_l).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      rewrite H9.
      apply transformed_prefix_sum_step.
      lia.
    + dump_pre_spatial. cancel (IntArray.full lst lst_size input_l).
Qed.

Lemma proof_of_p142_sum_squares_entail_wit_2_3 : p142_sum_squares_entail_wit_2_3.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full lst lst_size input_l).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      rewrite H9.
      apply transformed_prefix_sum_step.
      lia.
    + dump_pre_spatial. cancel (IntArray.full lst lst_size input_l).
Qed.

Lemma proof_of_p142_sum_squares_return_wit_1 : p142_sum_squares_return_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full lst_pre lst_size_pre input_l).
  - dump_pre_spatial.
    unfold problem_142_spec.
    assert (Hi : i = lst_size) by lia.
    subst i.
    rewrite H9.
    unfold transformed_prefix_sum.
    rewrite sublist_all by lia.
    reflexivity.
Qed.

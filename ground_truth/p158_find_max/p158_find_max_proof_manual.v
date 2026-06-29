Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import p158_find_max_goal.
From SimpleC.EE Require Import p158_find_max_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p158_find_max.
Local Open Scope sac.
Local Open Scope bool_scope.
Local Open Scope list_scope.

Lemma zeros_snoc_158 : forall k,
  0 <= k ->
  zeros k ++ 0 :: nil = zeros (k + 1).
Proof.
  intros k Hk.
  symmetry.
  unfold zeros.
  replace (Z.to_nat (k + 1)) with (Z.to_nat k + 1)%nat by lia.
  rewrite repeat_app.
  reflexivity.
Qed.

Axiom rows_well_formed_158_row : forall rows n k,
  rows_well_formed_158 rows n ->
  0 <= k < n ->
  let row := Znth k rows nil in
  let payload := row_payload_z_158 row in
  row = string_lib.c_string payload /\
  string_lib.valid_string payload /\
  string_lib.string_length payload < INT_MAX /\
  (forall j,
     0 <= j <= string_lib.string_length payload ->
     Z.of_nat
       (count_unique_chars
          (string_of_list_z_158 (firstn (Z.to_nat j) payload))) <= 128) /\
  row_unique_count_z_158 row <= 128 /\
  Zlength row = string_lib.string_length payload + 1.

Axiom row_payload_c_string_158 : forall payload,
  row_payload_z_158 (string_lib.c_string payload) = payload.

Axiom c_string_Zlength_158 : forall payload,
  Zlength (string_lib.c_string payload) = string_lib.string_length payload + 1.

Axiom rows_well_formed_158_char_bound : forall rows n i j,
  rows_well_formed_158 rows n ->
  0 <= i < n ->
  0 <= j < string_lib.string_length (row_payload_z_158 (Znth i rows nil)) ->
  0 <= Znth j (Znth i rows nil) 0 <= 127.

Axiom char_ptr_array2_missing_i_split_two_158 :
  forall x n i j row_i rows,
  0 <= i < n ->
  0 <= j < n ->
  i <> j ->
  ((x + i * sizeof(PTR)) # Ptr |-> row_i) **
  CharArray.full row_i (Zlength (Znth i rows nil)) (Znth i rows nil) **
  CharPtrArray2.missing_i x n i row_i rows |--
  EX row_j,
    char_ptr_array2_missing_two_158 x n i row_i j row_j rows **
    ((x + j * sizeof(PTR)) # Ptr |-> row_j) **
    CharArray.full row_j (Zlength (Znth j rows nil)) (Znth j rows nil) **
    CharArray.full row_i (Zlength (Znth i rows nil)) (Znth i rows nil).

Axiom char_ptr_array2_missing_two_merge_full_cstring_158 :
  forall x n i row_i j row_j rows,
  rows_well_formed_158 rows n ->
  0 <= i < n ->
  0 <= j < n ->
  i <> j ->
  ((x + j * sizeof(PTR)) # Ptr |-> row_j) **
  CharArray.full row_j
    (string_lib.string_length (row_payload_z_158 (Znth j rows nil)) + 1)
    (string_lib.c_string (row_payload_z_158 (Znth j rows nil))) **
  CharArray.full row_i
    (string_lib.string_length (row_payload_z_158 (Znth i rows nil)) + 1)
    (string_lib.c_string (row_payload_z_158 (Znth i rows nil))) **
  char_ptr_array2_missing_two_158 x n i row_i j row_j rows |--
  CharPtrArray2.full x n rows.

Axiom char_ptr_array2_missing_i_merge_full_158 :
  forall x n i row_i rows,
  0 <= i < n ->
  ((x + i * sizeof(PTR)) # Ptr |-> row_i) **
  CharArray.full row_i (Zlength (Znth i rows nil)) (Znth i rows nil) **
  CharPtrArray2.missing_i x n i row_i rows |--
  CharPtrArray2.full x n rows.

Axiom strcmp_result_lt_string_le_158 : forall s1 s2 ret,
  string_lib.valid_string s1 ->
  string_lib.valid_string s2 ->
  string_lib.strcmp_result s1 s2 ret ->
  ret < 0 ->
  string_le (string_of_list_z_158 s1) (string_of_list_z_158 s2).

Axiom strcmp_result_ge_string_le_158 : forall s1 s2 ret,
  string_lib.valid_string s1 ->
  string_lib.valid_string s2 ->
  string_lib.strcmp_result s1 s2 ret ->
  ret >= 0 ->
  string_le (string_of_list_z_158 s2) (string_of_list_z_158 s1).

Axiom reset_prefix_state_158_initial : forall seen_l,
  Zlength seen_l = 128 ->
  reset_prefix_state_158 0 seen_l.

Axiom reset_prefix_state_158_step : forall k seen_l,
  reset_prefix_state_158 k seen_l ->
  0 <= k < 128 ->
  reset_prefix_state_158 (k + 1) (replace_Znth k 0 seen_l).

Axiom reset_prefix_state_158_full_zero : forall k seen_l,
  reset_prefix_state_158 k seen_l ->
  k >= 128 ->
  k <= 128 ->
  seen_l = zeros 128.

Axiom count_scan_state_158_initial : forall row,
  count_scan_state_158 row 0 (zeros 128) 0.

Axiom count_scan_state_158_step_new : forall row j seen_l unique ch,
  string_lib.valid_string (row_payload_z_158 row) ->
  count_scan_state_158 row j seen_l unique ->
  0 <= j < string_lib.string_length (row_payload_z_158 row) ->
  0 <= ch < 128 ->
  ch = Znth j (row_payload_z_158 row) 0 ->
  Znth ch seen_l 0 = 0 ->
  count_scan_state_158 row (j + 1) (replace_Znth ch 1 seen_l) (unique + 1).

Axiom count_scan_state_158_step_seen : forall row j seen_l unique ch,
  count_scan_state_158 row j seen_l unique ->
  0 <= j < string_lib.string_length (row_payload_z_158 row) ->
  0 <= ch < 128 ->
  ch = Znth j (row_payload_z_158 row) 0 ->
  Znth ch seen_l 0 <> 0 ->
  count_scan_state_158 row (j + 1) seen_l unique.

Axiom count_scan_state_158_complete : forall row seen_l unique,
  count_scan_state_158
    row (string_lib.string_length (row_payload_z_158 row)) seen_l unique ->
  unique = row_unique_count_z_158 row.

Axiom best_prefix_state_158_final_spec : forall rows n best_idx maxu,
  rows_well_formed_158 rows n ->
  problem_158_pre_z rows ->
  0 < n ->
  best_prefix_state_158 rows n best_idx maxu ->
  problem_158_spec_z rows best_idx.

Lemma string_le_refl_158 : forall s,
  string_le s s.
Proof.
  induction s as [| c s IH]; simpl; auto.
Qed.

Lemma string_le_trans_158 : forall s1 s2 s3,
  string_le s1 s2 ->
  string_le s2 s3 ->
  string_le s1 s3.
Proof.
  induction s1 as [| a s1 IH]; intros s2 s3 H12 H23.
  - simpl. exact I.
  - destruct s2 as [| b s2]; simpl in H12; [contradiction|].
    destruct s3 as [| c s3]; simpl in H23; [contradiction|].
    simpl in *.
    destruct H12 as [Hab | [Hab H12]];
    destruct H23 as [Hbc | [Hbc H23]].
    + left. lia.
    + subst c. left. exact Hab.
    + subst b. left. exact Hbc.
    + subst b c. right. split; [reflexivity|].
      eapply IH; eauto.
Qed.

Lemma row_unique_count_nonneg_158 : forall row,
  0 <= row_unique_count_z_158 row.
Proof.
  intros row.
  unfold row_unique_count_z_158.
  lia.
Qed.

Lemma best_prefix_state_158_initial : forall rows,
  best_prefix_state_158 rows 0 0 0.
Proof.
  intros rows.
  unfold best_prefix_state_158.
  split.
  - rewrite Zlength_correct. lia.
  - left; repeat split; reflexivity.
Qed.

Lemma best_prefix_state_158_step_keep : forall rows k best_idx maxu curu,
  best_prefix_state_158 rows k best_idx maxu ->
  0 <= k < Zlength rows ->
  curu = row_unique_count_z_158 (Znth k rows nil) ->
  curu <= maxu ->
  (curu = maxu ->
    string_le
      (row_string_z_158 (Znth best_idx rows nil))
      (row_string_z_158 (Znth k rows nil))) ->
  best_prefix_state_158 rows (k + 1) best_idx maxu.
Proof.
  intros rows k best_idx maxu curu Hst Hk Hcur Hle Htie.
  unfold best_prefix_state_158 in *.
  destruct Hst as [Hrange Hcase].
  split; [lia|].
  destruct Hcase as [[Hk0 [Hbest Hmax]] |
                     [Hkpos [Hbest_range [Hmax [Hall Hlex]]]]].
  - subst k best_idx maxu.
    right.
    assert (Hcur0 : row_unique_count_z_158 (Znth 0 rows nil) = 0).
    {
      subst curu.
      pose proof (row_unique_count_nonneg_158 (Znth 0 rows nil)).
      lia.
    }
    repeat split; try lia; auto.
    + intros j Hj.
      assert (j = 0) by lia. subst j. lia.
    + intros j Hj Hcnt.
      assert (j = 0) by lia. subst j.
      apply string_le_refl_158.
  - right.
    repeat split; try lia; auto.
    + intros j Hj.
      assert (j < k \/ j = k) as [Hlt | ->] by lia.
      * apply Hall; lia.
      * subst curu. exact Hle.
    + intros j Hj Hcnt.
      assert (j < k \/ j = k) as [Hlt | ->] by lia.
      * apply Hlex; auto; lia.
      * apply Htie.
        subst curu. exact Hcnt.
Qed.

Lemma best_prefix_state_158_step_update_strict : forall rows k best_idx maxu curu,
  best_prefix_state_158 rows k best_idx maxu ->
  0 <= k < Zlength rows ->
  curu = row_unique_count_z_158 (Znth k rows nil) ->
  maxu < curu ->
  best_prefix_state_158 rows (k + 1) k curu.
Proof.
  intros rows k best_idx maxu curu Hst Hk Hcur Hgt.
  unfold best_prefix_state_158 in *.
  destruct Hst as [Hrange Hcase].
  split; [lia|].
  right.
  repeat split; try lia; auto.
  - intros j Hj.
    assert (j < k \/ j = k) as [Hlt | ->] by lia.
    + destruct Hcase as [[Hk0 _] |
                         [_ [_ [_ [Hall _]]]]].
      * lia.
      * specialize (Hall j ltac:(lia)). lia.
    + subst curu. lia.
  - intros j Hj Hcnt.
    assert (j < k \/ j = k) as [Hlt | ->] by lia.
    + destruct Hcase as [[Hk0 _] |
                         [_ [_ [_ [Hall _]]]]].
      * lia.
      * specialize (Hall j ltac:(lia)). lia.
    + apply string_le_refl_158.
Qed.

Lemma best_prefix_state_158_step_update_tie : forall rows k best_idx maxu curu,
  best_prefix_state_158 rows k best_idx maxu ->
  0 <= k < Zlength rows ->
  curu = row_unique_count_z_158 (Znth k rows nil) ->
  curu = maxu ->
  string_le
    (row_string_z_158 (Znth k rows nil))
    (row_string_z_158 (Znth best_idx rows nil)) ->
  best_prefix_state_158 rows (k + 1) k curu.
Proof.
  intros rows k best_idx maxu curu Hst Hk Hcur Htie_count Htie_lex.
  unfold best_prefix_state_158 in *.
  destruct Hst as [Hrange Hcase].
  split; [lia|].
  right.
  split; [lia|].
  split; [lia|].
  split; [exact Hcur|].
  split.
  - intros j Hj.
    assert (j < k \/ j = k) as [Hlt | ->] by lia.
    + destruct Hcase as [[Hk0 _] |
                         [_ [_ [Hmax [Hall _]]]]].
      * lia.
      * specialize (Hall j ltac:(lia)). subst curu. lia.
    + subst curu. lia.
  - intros j Hj Hcnt.
    assert (j < k \/ j = k) as [Hlt | ->] by lia.
    + destruct Hcase as [[Hk0 _] |
                         [_ [_ [Hmax [_ Hlex]]]]].
      * lia.
      * eapply string_le_trans_158.
        -- exact Htie_lex.
        -- apply Hlex.
           ++ lia.
           ++ subst curu. lia.
    + apply string_le_refl_158.
Qed.

Local Close Scope bool_scope.

Lemma proof_of_find_max_entail_wit_1 : find_max_entail_wit_1.
Proof.
  pre_process_default.
  unfold zeros; simpl.
  rewrite IntArray.seg_empty.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_2 : find_max_entail_wit_2.
Proof.
  pre_process_default.
  rewrite zeros_snoc_158 by lia.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_3 : find_max_entail_wit_3.
Proof.
  pre_process_default.
  subst.
  Exists (zeros 128).
  replace k with 128 by lia.
  rewrite (IntArray.undef_seg_empty ( &( "seen" ) ) 128).
  sep_apply (IntArray.seg_to_full ( &( "seen" ) ) 0 128 (zeros 128)).
  replace ((&( "seen" ) + 0 * sizeof(INT))) with (&( "seen" )) by lia.
  replace (128 - 0) with 128 by lia.
  entailer!.
  apply best_prefix_state_158_initial.
Qed.

Lemma proof_of_find_max_entail_wit_4 : find_max_entail_wit_4.
Proof.
  pre_process_default.
  prop_apply (CharPtrArray2.full_Zlength words_pre words_size_pre rows).
  Intros.
  sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i words_pre i words_size_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr seen_l_2.
    unfold StorePtrAsElement.storeA.
    rewrite sizeof_ptr.
    repeat match goal with
    | |- context [Znth i rows ?d] => rewrite (Znth_indep rows i nil d) by lia
    end.
    entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_5 : find_max_entail_wit_5.
Proof.
  pre_process_default.
  Exists row_ptr_2 seen_l_2.
  entailer!.
  apply reset_prefix_state_158_initial; auto.
Qed.

Lemma proof_of_find_max_entail_wit_6 : find_max_entail_wit_6.
Proof.
  pre_process_default.
  Exists row_ptr_2 (replace_Znth k 0 seen_l_2).
  entailer!.
  - apply reset_prefix_state_158_step; auto; lia.
  - rewrite Zlength_replace_Znth; lia.
Qed.

Lemma proof_of_find_max_entail_wit_7 : find_max_entail_wit_7.
Proof.
  pre_process_default.
  assert (seen_l = zeros 128) as ->.
  { eapply reset_prefix_state_158_full_zero; eauto; lia. }
  Exists row_ptr_2.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_8 : find_max_entail_wit_8.
Proof.
  pre_process_default.
  match goal with
  | Hwf : rows_well_formed_158 rows words_size_pre |- _ =>
      pose proof (rows_well_formed_158_row rows words_size_pre i Hwf ltac:(lia)) as Hrow_info
  end.
  destruct Hrow_info as [Hrow [Hvalid [Hlt [_ [_ Hlen]]]]].
  rewrite Hrow.
  unfold store_string.
  rewrite row_payload_c_string_158.
  rewrite c_string_Zlength_158.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_9 : find_max_entail_wit_9.
Proof.
  pre_process_default.
  Exists (zeros 128).
  match goal with
  | Hwf : rows_well_formed_158 rows words_size_pre |- _ =>
      pose proof (rows_well_formed_158_row rows words_size_pre i Hwf ltac:(lia))
        as Hrow_info
  end.
  destruct Hrow_info as [Hrow [Hvalid [Hlt [Hprefix [Hbound Hlen]]]]].
  assert (0 <= retval) by (rewrite PreH1; unfold string_length; apply Zlength_nonneg).
  unfold store_string.
  rewrite <- Hrow.
  rewrite <- Hlen.
  entailer!.
  apply count_scan_state_158_initial.
Qed.

Lemma proof_of_find_max_entail_wit_10 : find_max_entail_wit_10.
Proof.
  pre_process_default.
  match goal with
  | Hwf : rows_well_formed_158 rows words_size_pre |- _ =>
      pose proof (rows_well_formed_158_char_bound rows words_size_pre i j
        Hwf ltac:(lia) ltac:(lia)) as Hchar_bound
  end.
  Exists seen_l_2.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_11_1 : find_max_entail_wit_11_1.
Proof.
  pre_process_default.
  pose proof (rows_well_formed_158_row rows words_size_pre i PreH22 ltac:(lia))
    as Hrow_info.
  destruct Hrow_info as [Hrow [Hvalid [Hlt [Hprefix [Hbound Hlen]]]]].
  assert (Hch_payload : ch = Znth j (row_payload_z_158 (Znth i rows nil)) 0).
  {
    rewrite Hrow in PreH11.
    rewrite string_lib.c_string_Znth_inside in PreH11 by (rewrite <- PreH18; lia).
    exact PreH11.
  }
  assert (Hnew_state :
    count_scan_state_158
      (Znth i rows nil) (j + 1) (replace_Znth ch 1 seen_l_2) (unique + 1)).
  { eapply count_scan_state_158_step_new; eauto; lia. }
  assert (Hunique_bound : unique + 1 <= 128).
  {
    unfold count_scan_state_158 in Hnew_state.
    destruct Hnew_state as [_ [_ [_ Huniq_new]]].
    rewrite Huniq_new.
    apply Hprefix. rewrite <- PreH18. lia.
  }
  Exists (replace_Znth ch 1 seen_l_2).
  entailer!.
  rewrite Zlength_replace_Znth; lia.
Qed.

Lemma proof_of_find_max_entail_wit_11_2 : find_max_entail_wit_11_2.
Proof.
  pre_process_default.
  pose proof (rows_well_formed_158_row rows words_size_pre i PreH22 ltac:(lia))
    as Hrow_info.
  destruct Hrow_info as [Hrow [Hvalid [Hlt [Hprefix [Hbound Hlen]]]]].
  assert (Hch_payload : ch = Znth j (row_payload_z_158 (Znth i rows nil)) 0).
  {
    rewrite Hrow in PreH11.
    rewrite string_lib.c_string_Znth_inside in PreH11 by (rewrite <- PreH18; lia).
    exact PreH11.
  }
  Exists seen_l_2.
  entailer!.
  eapply count_scan_state_158_step_seen; eauto; lia.
Qed.

Lemma proof_of_find_max_entail_wit_12 : find_max_entail_wit_12.
Proof.
  pre_process_default.
  assert (Hj_len : j = string_lib.string_length (row_payload_z_158 (Znth i rows nil))).
  { rewrite <- PreH17. lia. }
  assert (Hunique_final : unique = row_unique_count_z_158 (Znth i rows nil)).
  {
    rewrite Hj_len in PreH26.
    eapply count_scan_state_158_complete; exact PreH26.
  }
  pose proof (rows_well_formed_158_row rows words_size_pre i PreH23 ltac:(lia))
    as Hcur_info.
  pose proof (rows_well_formed_158_row rows words_size_pre best_idx PreH23 ltac:(lia))
    as Hbest_info.
  destruct Hcur_info as [Hcur_row [Hcur_valid [Hcur_lt [_ [_ Hcur_len]]]]].
  destruct Hbest_info as [Hbest_row [Hbest_valid [Hbest_lt [_ [_ Hbest_len]]]]].
  sep_apply_l_atomic
    (char_ptr_array2_missing_i_split_two_158
      words_pre words_size_pre i best_idx row_ptr rows ltac:(lia) ltac:(lia) PreH1).
  Intros best_ptr.
  Exists best_ptr seen_l_2.
  rewrite Hcur_row in Hcur_len.
  rewrite Hbest_row in Hbest_len.
  rewrite Hcur_row.
  rewrite Hbest_row.
  rewrite !row_payload_c_string_158 in *.
  unfold store_string.
  rewrite <- Hcur_len, <- Hbest_len.
  entailer!.
  rewrite <- Hcur_row.
  exact Hunique_final.
Qed.

Lemma proof_of_find_max_entail_wit_15_1 : find_max_entail_wit_15_1.
Proof.
  pre_process_default.
  - assert (Hj_len : j = string_lib.string_length (row_payload_z_158 (Znth i rows nil))).
    { rewrite <- PreH17. lia. }
    assert (Hunique_final : unique = row_unique_count_z_158 (Znth i rows nil)).
    {
      rewrite Hj_len in PreH26.
      eapply count_scan_state_158_complete; exact PreH26.
    }
    pose proof (proj1 PreH23) as Hrows_len.
    pose proof (rows_well_formed_158_row rows words_size_pre i PreH23 ltac:(lia))
      as Hrow_info.
    destruct Hrow_info as [_ [_ [Hlen_lt [_ [_ _]]]]].
    assert (Hstep : best_prefix_state_158 rows (i + 1) best_idx maxu).
    {
      eapply best_prefix_state_158_step_keep
        with (curu := unique); eauto; try lia.
      intros _.
      subst best_idx.
      apply string_le_refl_158.
    }
    sep_apply_l_atomic
      (char_ptr_array2_missing_i_merge_full_158
        words_pre words_size_pre i row_ptr rows ltac:(lia)).
    Exists seen_l_2.
    entailer!.
  Unshelve.
  all: try lia; try entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_15_2 : find_max_entail_wit_15_2.
Proof.
  pre_process_default.
  assert (Hj_len : j = string_lib.string_length (row_payload_z_158 (Znth i rows nil))).
  { rewrite <- PreH16. lia. }
  assert (Hunique_final : unique = row_unique_count_z_158 (Znth i rows nil)).
  {
    rewrite Hj_len in PreH25.
    eapply count_scan_state_158_complete; exact PreH25.
  }
  pose proof (proj1 PreH22) as Hrows_len.
  pose proof (rows_well_formed_158_row rows words_size_pre i PreH22 ltac:(lia))
    as Hrow_info.
  destruct Hrow_info as [_ [_ [Hlen_lt [_ [_ _]]]]].
  assert (Hstep : best_prefix_state_158 rows (i + 1) best_idx maxu).
  {
    eapply best_prefix_state_158_step_keep
      with (curu := unique); eauto; try lia.
  }
  sep_apply_l_atomic
    (char_ptr_array2_missing_i_merge_full_158
      words_pre words_size_pre i row_ptr rows ltac:(lia)).
  Exists seen_l_2.
  entailer!.
  Unshelve.
  all: try lia; try entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_15_3 : find_max_entail_wit_15_3.
Proof.
  right.
  pre_process_default.
  pose proof (proj1 PreH17) as Hrows_len.
  assert (Hstep : best_prefix_state_158 rows (i + 1) best_idx maxu).
  {
    eapply best_prefix_state_158_step_keep
      with (curu := unique).
    - exact PreH19.
    - lia.
    - exact PreH11.
    - lia.
    - intros _.
      subst unique.
      eapply strcmp_result_ge_string_le_158; eauto; lia.
  }
  sep_apply_l_atomic
    (char_ptr_array2_missing_two_merge_full_cstring_158
      words_pre words_size_pre i row_ptr best_idx best_ptr rows
      PreH17 ltac:(lia) ltac:(lia) ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_15_4 : find_max_entail_wit_15_4.
Proof.
  right.
  pre_process_default.
  pose proof (proj1 PreH17) as Hrows_len.
  assert (Htie :
    string_le
      (row_string_z_158 (Znth i rows nil))
      (row_string_z_158 (Znth best_idx rows nil))).
  {
    eapply strcmp_result_lt_string_le_158; eauto; lia.
  }
  assert (Hstep : best_prefix_state_158 rows (i + 1) i maxu).
  {
    assert (Hstep_unique : best_prefix_state_158 rows (i + 1) i unique).
    {
      eapply best_prefix_state_158_step_update_tie
        with (best_idx := best_idx) (maxu := maxu); eauto; try lia.
    }
    rewrite PreH12 in Hstep_unique.
    exact Hstep_unique.
  }
  sep_apply_l_atomic
    (char_ptr_array2_missing_two_merge_full_cstring_158
      words_pre words_size_pre i row_ptr best_idx best_ptr rows
      PreH17 ltac:(lia) ltac:(lia) ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_15_5 : find_max_entail_wit_15_5.
Proof.
  pre_process_default.
  assert (Hj_len : j = string_lib.string_length (row_payload_z_158 (Znth i rows nil))).
  { rewrite <- PreH15. lia. }
  assert (Hunique_final : unique = row_unique_count_z_158 (Znth i rows nil)).
  {
    rewrite Hj_len in PreH24.
    eapply count_scan_state_158_complete; exact PreH24.
  }
  pose proof (rows_well_formed_158_row rows words_size_pre i PreH21 ltac:(lia))
    as Hrow_info.
  pose proof (proj1 PreH21) as Hrows_len.
  destruct Hrow_info as [_ [_ [Hlen_lt [_ [_ _]]]]].
  assert (Hstep : best_prefix_state_158 rows (i + 1) i unique).
  {
    eapply best_prefix_state_158_step_update_strict
      with (best_idx := best_idx) (maxu := maxu).
    - exact PreH23.
    - lia.
    - exact Hunique_final.
    - lia.
  }
  sep_apply_l_atomic
    (char_ptr_array2_missing_i_merge_full_158
      words_pre words_size_pre i row_ptr rows ltac:(lia)).
  Exists seen_l_2.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_17 : find_max_entail_wit_17.
Proof.
  pre_process_default.
  assert (Hi_end : i = words_size_pre) by lia.
  subst i.
  assert (Hspec : problem_158_spec_z rows best_idx).
  {
    eapply best_prefix_state_158_final_spec; eauto; lia.
  }
  prop_apply (CharPtrArray2.full_Zlength words_pre words_size_pre rows).
  Intros.
  sep_apply_l_atomic
    (CharPtrArray2.full_split_to_missing_i
      words_pre best_idx words_size_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr seen_l_2.
    unfold StorePtrAsElement.storeA.
    rewrite sizeof_ptr.
    repeat match goal with
    | |- context [Znth best_idx rows ?d] =>
        rewrite (Znth_indep rows best_idx nil d) by lia
    end.
    entailer!.
Qed.

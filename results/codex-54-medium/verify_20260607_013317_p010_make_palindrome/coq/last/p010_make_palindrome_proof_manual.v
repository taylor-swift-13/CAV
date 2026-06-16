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
From SimpleC.EE.CAV.verify_20260607_013317_p010_make_palindrome Require Import p010_make_palindrome_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p010_make_palindrome.
Require Import string_bridge.
Local Open Scope sac.

Lemma proof_of_is_pal_suffix_entail_wit_2 : is_pal_suffix_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  intros k Hk.
  destruct (Z.eq_dec k (i - start_pre)) as [-> | Hneq].
  - replace (start_pre + (i - start_pre)) with i by lia.
    replace (n_pre - 1 - (i - start_pre)) with j by lia.
    rewrite !app_Znth1 in H; try (rewrite H5; lia).
    exact H.
  - apply H11.
    lia.
Qed.

Lemma proof_of_is_pal_suffix_return_wit_1 : is_pal_suffix_return_wit_1.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  entailer!.
  unfold pal_suffix.
  split; [lia|].
  intros k Hk1 Hk2.
  match goal with
  | Hlen : Zlength l = n_pre,
    Hinv : (forall k_2 : Z, 0 <= k_2 < i - start_pre ->
              Znth (start_pre + k_2) l 0 = Znth (n_pre - 1 - k_2) l 0)
    |- _ =>
      rewrite Hlen; apply Hinv; lia
  end.
Qed.

Lemma proof_of_is_pal_suffix_return_wit_2 : is_pal_suffix_return_wit_2.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros2.
  entailer!.
  unfold pal_suffix.
  intros [_ Hpal].
  assert (Hi_range : 0 <= i - start_pre < Zlength l - start_pre).
  { match goal with Hlen : Zlength l = n_pre |- _ => rewrite Hlen; lia end. }
  assert (Hi_mid : i - start_pre < Zlength l - start_pre - 1 - (i - start_pre)).
  { match goal with Hlen : Zlength l = n_pre |- _ => rewrite Hlen; lia end. }
  specialize (Hpal (i - start_pre) Hi_range Hi_mid).
  replace (start_pre + (i - start_pre)) with i in Hpal by lia.
  replace (Zlength l - 1 - (i - start_pre)) with j in Hpal.
  2:{ match goal with Hlen : Zlength l = n_pre |- _ => rewrite Hlen; lia end. }
  match goal with
  | Hneq : Znth i (l ++ 0 :: nil) 0 <> Znth j (l ++ 0 :: nil) 0 |- _ =>
      rewrite !app_Znth1 in Hneq; try (match goal with Hlen : Zlength l = n_pre |- _ => rewrite Hlen; lia end);
      congruence
  end.
Qed.

Lemma proof_of_is_pal_suffix_return_wit_3 : is_pal_suffix_return_wit_3.
Proof.
  pre_process.
  rewrite <- derivable1_orp_intros1.
  entailer!.
  unfold pal_suffix.
  split; [lia|].
  intros k Hk1 Hk2.
  lia.
Qed.

Lemma proof_of_p010_make_palindrome_entail_wit_3_1 : p010_make_palindrome_entail_wit_3_1.
Proof.
  pre_process.
  right.
  unfold first_pal_suffix.
  unfold pal_suffix in H2.
  destruct H2 as [H2range H2pal].
  entailer!.
  repeat split; try entailer!; try assumption; try lia; try (apply H9; lia); try exact H2pal.
  1: change (0 <= i + 1); lia.
  2: unfold coq_prop; lia.
  unfold coq_prop; lia.
Qed.

Lemma proof_of_p010_make_palindrome_entail_wit_3_2 : p010_make_palindrome_entail_wit_3_2.
Proof.
  pre_process.
  left.
  entailer!.
  repeat split; try entailer!; try assumption; try lia; try (apply H9; lia).
  - change (0 <= i + 1); lia.
  - unfold coq_prop; lia.
  - unfold coq_prop.
    intros t Ht.
    destruct (Z.eq_dec t i) as [-> | Hneq].
    + exact H2.
    + apply H13.
      lia.
Qed.

Lemma proof_of_p010_make_palindrome_entail_wit_4_1 : p010_make_palindrome_entail_wit_4_1.
Proof.
  pre_process.
  assert (2147483647 ÷ 2 = 1073741823) by (vm_compute; reflexivity).
  entailer!.
Qed.

Lemma proof_of_p010_make_palindrome_entail_wit_4_2 : p010_make_palindrome_entail_wit_4_2.
Proof.
  pre_process.
  assert (2147483647 ÷ 2 = 1073741823) by (vm_compute; reflexivity).
  unfold first_pal_suffix in H10.
  destruct H10 as [[_ Hbestlen] [_ _]].
  entailer!.
Qed.

Lemma proof_of_p010_make_palindrome_entail_wit_5 : p010_make_palindrome_entail_wit_5.
Proof.
  pre_process.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval (len + best + 1)).
  change (sublist 0 0 l) with (@nil Z).
  rewrite (CharArray.full_empty retval 0).
  split_pure_spatial.
  - cancel (CharArray.undef_seg retval 0 (len + best + 1)).
    cancel (CharArray.full str_pre (len + 1) (l ++ 0 :: nil)).
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_p010_make_palindrome_entail_wit_6 : p010_make_palindrome_entail_wit_6.
Proof.
  pre_process.
  assert (Hlen : len <= Zlength l).
  {
    destruct (Z_le_gt_dec len (Zlength l)) as [Hle | Hgt]; [lia |].
    pose proof (Zlength_nonneg l) as Hzlen.
    specialize (H13 (Zlength l)).
    assert (Znth (Zlength l) l 0 <> 0) by (apply H13; lia).
    assert (Znth (Zlength l) l 0 = 0) as Hz.
    {
      unfold Znth.
      rewrite Zlength_correct.
      rewrite nth_overflow by lia.
      reflexivity.
    }
    contradiction.
  }
  assert (Hi : i < Zlength l).
  {
    lia.
  }
  replace (sublist 0 (i + 1) l)
    with (app (sublist 0 i l) (Znth i (app l (0 :: nil)) 0 :: nil)).
  2: {
    rewrite (sublist_split 0 (i + 1) i l) by lia.
    rewrite (sublist_single 0 i l) by lia.
    rewrite app_Znth1 by lia.
    reflexivity.
  }
  split_pure_spatial.
  - cancel (CharArray.full out (i + 1)
      (app (sublist 0 i l) (Znth i (app l (0 :: nil)) 0 :: nil))).
    cancel (CharArray.undef_seg out (i + 1) (out_len + 1)).
    cancel (CharArray.full str_pre (len + 1) (app l (0 :: nil))).
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_p010_make_palindrome_entail_wit_7 : p010_make_palindrome_entail_wit_7.
Proof.
  pre_process.
  prop_apply (CharArray.full_Zlength str_pre (len + 1) (app l (0 :: nil))).
  entailer!.
  assert (Hi : i = len) by lia.
  subst i.
  assert (Hzl : Zlength l = len).
  {
    lazymatch goal with
    | Hlen : Zlength (l ++ 0 :: nil) = len + 1 |- _ =>
        rewrite Zlength_app in Hlen;
        simpl in Hlen;
        rewrite Zlength_cons in Hlen;
        rewrite Zlength_nil in Hlen;
        lia
    end.
  }
  rewrite (sublist_self l len) by exact (eq_sym Hzl).
  replace (rev (sublist (best - 0) best l)) with (@nil Z).
  2: {
    replace (best - 0) with best by lia.
    unfold sublist.
    rewrite skipn_all2.
    - reflexivity.
    - rewrite length_firstn. lia.
  }
  simpl app.
  replace (len + 0) with len by lia.
  rewrite app_nil_r.
  cancel.
Qed.

Lemma proof_of_p010_make_palindrome_entail_wit_8 : p010_make_palindrome_entail_wit_8.
Proof.
  pre_process.
  prop_apply (CharArray.full_Zlength str_pre (len + 1) (app l (0 :: nil))).
  entailer!.
  assert (Hzl : Zlength l = len).
  {
    lazymatch goal with
    | Hlen : Zlength (l ++ 0 :: nil) = len + 1 |- _ =>
        rewrite Zlength_app in Hlen;
        simpl in Hlen;
        rewrite Zlength_cons in Hlen;
        rewrite Zlength_nil in Hlen;
        lia
    end.
  }
  replace (app l (rev (sublist (best - (k + 1)) best l)))
    with (app (app l (rev (sublist (best - k) best l)))
          (Znth ((best - 1) - k) (app l (0 :: nil)) 0 :: nil)).
  2: {
    rewrite (sublist_split (best - (k + 1)) best (best - k) l) by lia.
    replace (best - k) with (best - (k + 1) + 1) by lia.
    rewrite (sublist_single 0 (best - (k + 1)) l) by lia.
    rewrite rev_app_distr.
    simpl.
    replace (best - (k + 1)) with ((best - 1) - k) by lia.
    rewrite app_Znth1 by lia.
    rewrite app_assoc.
    reflexivity.
  }
  rewrite <- app_assoc.
  replace (len + (k + 1)) with (len + k + 1) by lia.
  cancel.
Qed.

Lemma proof_of_p010_make_palindrome_entail_wit_9 : p010_make_palindrome_entail_wit_9.
Proof.
  pre_process.
  assert (k = best) by lia.
  subst k.
  replace (best - best) with 0 by lia.
  entailer!.
Qed.

Lemma proof_of_p010_make_palindrome_return_wit_1 : p010_make_palindrome_return_wit_1.
Proof.
  pre_process.
  Exists (app l (rev (sublist 0 best l))).
  entailer!.
Qed.

Lemma proof_of_p010_make_palindrome_partial_solve_wit_1_pure : p010_make_palindrome_partial_solve_wit_1_pure.
Proof.
  pre_process.
  assert (INT_MAX ÷ 2 < INT_MAX) by (vm_compute; lia).
  entailer!.
Qed.

Lemma proof_of_p010_make_palindrome_partial_solve_wit_2_pure : p010_make_palindrome_partial_solve_wit_2_pure.
Proof.
  pre_process.
  entailer!.
Qed.

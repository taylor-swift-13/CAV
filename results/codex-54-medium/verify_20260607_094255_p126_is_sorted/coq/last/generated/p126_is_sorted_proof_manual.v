Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260607_094255_p126_is_sorted Require Import p126_is_sorted_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p126_is_sorted.
Local Open Scope sac.

Lemma sorted_no_triple_prefix_1 : forall lv, sorted_no_triple_prefix 1 lv.
Proof.
  intros lv.
  unfold sorted_no_triple_prefix.
  split; intros j Hj; lia.
Qed.

Lemma sorted_no_triple_prefix_extend :
  forall lv i,
    sorted_no_triple_prefix i lv ->
    1 <= i ->
    Znth (i - 1) lv 0 <= Znth i lv 0 ->
    (i < 2 \/ Znth i lv 0 <> Znth (i - 1) lv 0 \/ Znth i lv 0 <> Znth (i - 2) lv 0) ->
    sorted_no_triple_prefix (i + 1) lv.
Proof.
  intros lv i [Hord Htriple] Hi Hstep Hfresh.
  unfold sorted_no_triple_prefix.
  split.
  - intros j Hj.
    destruct (Z_lt_ge_dec j i) as [Hlt | Hge].
    + apply Hord; lia.
    + assert (j = i) by lia. subst j. exact Hstep.
  - intros j Hj [Heq1 Heq2].
    destruct (Z_lt_ge_dec j i) as [Hlt | Hge].
    + apply (Htriple j); lia.
    + assert (j = i) by lia. subst j.
      destruct Hfresh as [Hsmall | [Hneq1 | Hneq2]]; lia || congruence.
Qed.

Lemma proof_of_p126_is_sorted_entail_wit_1 : p126_is_sorted_entail_wit_1.
Proof.
  pre_process.
  Exists (sublist 0 1 lv) (sublist 1 (Zlength lv) lv).
  entailer!.
  - apply sorted_no_triple_prefix_1.
  - rewrite Zlength_sublist0; lia.
  - transitivity (sublist 0 (Zlength lv) lv).
    + replace (sublist 0 (Zlength lv) lv) with (sublist 0 (Zlength lv) (lv ++ nil)).
      * rewrite sublist_app_exact1. reflexivity.
      * rewrite app_nil_r. reflexivity.
    + apply sublist_split; lia.
Qed.

Lemma proof_of_p126_is_sorted_entail_wit_4_1 : p126_is_sorted_entail_wit_4_1.
Proof.
  pre_process.
  Exists (sublist 0 (i + 1) lv) (sublist (i + 1) (Zlength lv) lv).
  entailer!.
  - match goal with
    | Hsorted : sorted_no_triple_prefix i lv,
      Hge1 : 1 <= i,
      Hmono : Znth i lv 0 >= Znth (i - 1) lv 0,
      Hneq : Znth i lv 0 <> Znth (i - 1) lv 0 |- _ =>
        eapply sorted_no_triple_prefix_extend; [exact Hsorted | exact Hge1 | lia | right; left; exact Hneq]
    end.
  - rewrite Zlength_sublist0; lia.
  - transitivity (sublist 0 (Zlength lv) lv).
    + replace (sublist 0 (Zlength lv) lv) with (sublist 0 (Zlength lv) (lv ++ nil)).
      * rewrite sublist_app_exact1. reflexivity.
      * rewrite app_nil_r. reflexivity.
    + apply sublist_split; lia.
Qed.

Lemma proof_of_p126_is_sorted_entail_wit_4_2 : p126_is_sorted_entail_wit_4_2.
Proof.
  pre_process.
  Exists (sublist 0 (i + 1) lv) (sublist (i + 1) (Zlength lv) lv).
  entailer!.
  - match goal with
    | Hsorted : sorted_no_triple_prefix i lv,
      Hge1 : 1 <= i,
      Hmono : Znth i lv 0 >= Znth (i - 1) lv 0,
      Hsmall : i < 2 |- _ =>
        eapply sorted_no_triple_prefix_extend; [exact Hsorted | exact Hge1 | lia | left; exact Hsmall]
    end.
  - rewrite Zlength_sublist0; lia.
  - transitivity (sublist 0 (Zlength lv) lv).
    + replace (sublist 0 (Zlength lv) lv) with (sublist 0 (Zlength lv) (lv ++ nil)).
      * rewrite sublist_app_exact1. reflexivity.
      * rewrite app_nil_r. reflexivity.
    + apply sublist_split; lia.
Qed.

Lemma proof_of_p126_is_sorted_entail_wit_4_3 : p126_is_sorted_entail_wit_4_3.
Proof.
  pre_process.
  Exists (sublist 0 (i + 1) lv) (sublist (i + 1) (Zlength lv) lv).
  entailer!.
  - match goal with
    | Hsorted : sorted_no_triple_prefix i lv,
      Hge1 : 1 <= i,
      Hmono : Znth i lv 0 >= Znth (i - 1) lv 0,
      Hneq : Znth i lv 0 <> Znth (i - 2) lv 0 |- _ =>
        eapply sorted_no_triple_prefix_extend; [exact Hsorted | exact Hge1 | lia | right; right; exact Hneq]
    end.
  - rewrite Zlength_sublist0; lia.
  - transitivity (sublist 0 (Zlength lv) lv).
    + replace (sublist 0 (Zlength lv) lv) with (sublist 0 (Zlength lv) (lv ++ nil)).
      * rewrite sublist_app_exact1. reflexivity.
      * rewrite app_nil_r. reflexivity.
    + apply sublist_split; lia.
Qed.

Lemma proof_of_p126_is_sorted_return_wit_1 : p126_is_sorted_return_wit_1.
Proof.
  pre_process.
  assert (Hspec : problem_126_spec lv true).
  {
    unfold problem_126_spec.
    split.
    - intros _. reflexivity.
    - intros _.
      match goal with
      | Hlen : lst_size_pre = Zlength lv,
        Hge : i >= lst_size_pre,
        Hle : i <= lst_size_pre,
        Hsorted : sorted_no_triple_prefix i lv |- _ =>
          replace (Zlength lv) with i by lia; exact Hsorted
      end.
  }
  right.
  entailer!.
  split.
  - cbv. intros C. lia.
  - split.
    + exact Hspec.
    + match goal with
      | Hfull : IntArray.full lst_pre lst_size_pre lv m |- _ => exact Hfull
      end.
Qed.

Lemma proof_of_p126_is_sorted_return_wit_2 : p126_is_sorted_return_wit_2.
Proof.
  pre_process.
  assert (Hspec : problem_126_spec lv false).
  {
    unfold problem_126_spec.
    split.
    - intros Hfull.
      destruct Hfull as [_ Htriple].
      exfalso.
      assert (Hrange : 2 <= i < Zlength lv) by lia.
      specialize (Htriple i Hrange).
      apply Htriple.
      split; assumption.
    - intros Hfalse. discriminate.
  }
  left.
  entailer!.
  split.
  - cbv. reflexivity.
  - split.
    + exact Hspec.
    + match goal with
      | Hfull : IntArray.full lst_pre lst_size_pre lv m |- _ => exact Hfull
      end.
Qed.

Lemma proof_of_p126_is_sorted_return_wit_3 : p126_is_sorted_return_wit_3.
Proof.
  pre_process.
  assert (Hspec : problem_126_spec lv false).
  {
    unfold problem_126_spec.
    split.
    - intros Hfull.
      destruct Hfull as [Hord _].
      exfalso.
      specialize (Hord i).
      lia.
    - intros Hfalse. discriminate.
  }
  left.
  entailer!.
  split.
  - cbv. reflexivity.
  - split.
    + exact Hspec.
    + match goal with
      | Hfull : IntArray.full lst_pre lst_size_pre lv m |- _ => exact Hfull
      end.
Qed.

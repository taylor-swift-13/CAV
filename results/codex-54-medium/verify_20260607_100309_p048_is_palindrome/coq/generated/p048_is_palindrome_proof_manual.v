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
From SimpleC.EE.CAV.verify_20260607_100309_p048_is_palindrome Require Import p048_is_palindrome_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p048_is_palindrome.
Local Open Scope sac.

Lemma proof_of_p048_is_palindrome_entail_wit_2 : p048_is_palindrome_entail_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full text_pre (n + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial. exact H1.
    + dump_pre_spatial. exact H2.
    + dump_pre_spatial. exact H3.
    + dump_pre_spatial. exact H6.
    + dump_pre_spatial. exact H0.
    + dump_pre_spatial. exact H9.
    + dump_pre_spatial. exact H10.
    + dump_pre_spatial. exact H11.
    + dump_pre_spatial. exact H12.
    + dump_pre_spatial.
      rewrite app_Znth1 in H by lia.
      rewrite app_Znth1 in H by lia.
      exact H.
Qed.

Lemma proof_of_p048_is_palindrome_entail_wit_3 : p048_is_palindrome_entail_wit_3.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full text_pre (n + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial; exact H1.
    + dump_pre_spatial; exact H2.
    + dump_pre_spatial; exact H3.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; exact H11.
    + dump_pre_spatial.
      intros k Hk.
      destruct (Z.eq_dec k i) as [-> | Hneq].
      * rewrite app_Znth1 in H by lia.
        rewrite app_Znth1 in H by lia.
        replace j with (n - 1 - i) in H by lia.
        exact H.
      * apply H12; lia.
Qed.

Lemma proof_of_p048_is_palindrome_return_wit_1 : p048_is_palindrome_return_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full text_pre (n + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial; exact H9.
    + dump_pre_spatial.
      unfold problem_48_spec, bool_of, palindrome.
      split.
      * intros _ k Hk Hlt.
        assert (Hki : k < i).
        { destruct (Z_lt_ge_dec k i) as [Hki | Hki]; auto.
          assert (Hmirror_le_j : n - 1 - k <= j) by lia.
          lia. }
        replace (Zlength l - 1 - k) with (n - 1 - k) by lia.
        apply H10; lia.
      * intros _. reflexivity.
Qed.

Lemma proof_of_p048_is_palindrome_return_wit_2 : p048_is_palindrome_return_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full text_pre (n + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial; exact H8.
    + dump_pre_spatial.
      unfold problem_48_spec, bool_of, palindrome.
      split.
      * discriminate.
      * intros Hpal.
        specialize (Hpal i).
        assert (Hrange : 0 <= i < Zlength l) by lia.
        assert (Hlt : i < Zlength l - 1 - i) by lia.
        specialize (Hpal Hrange Hlt).
        replace (Zlength l - 1 - i) with j in Hpal by lia.
        contradiction.
Qed.

Lemma proof_of_p048_is_palindrome_return_wit_3 : p048_is_palindrome_return_wit_3.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full text_pre (n + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial; exact H7.
    + dump_pre_spatial.
      assert (n = 0) by lia.
      subst n.
      assert (Hl : l = nil).
      { apply Zlength_nil_inv. lia. }
      subst l.
      unfold problem_48_spec, bool_of, palindrome.
      split.
      * intros _. intros k Hk. lia.
      * intros _. reflexivity.
Qed.

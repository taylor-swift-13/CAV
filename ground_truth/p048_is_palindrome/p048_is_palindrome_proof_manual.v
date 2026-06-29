Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p048_is_palindrome Require Import p048_is_palindrome_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Require Import Lia.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import string_bridge.
Require Import p048_is_palindrome.
Local Open Scope sac.

Lemma proof_of_p048_is_palindrome_entail_wit_2 : p048_is_palindrome_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  intros k Hk.
  destruct (Z.eq_dec k i) as [-> | Hneq].
  - match goal with
    | Heq : Znth i (app l (0 :: nil)) 0 = Znth j (app l (0 :: nil)) 0 |- _ =>
        rewrite (app_Znth1 0 l (0 :: nil) i) in Heq by lia;
        rewrite (app_Znth1 0 l (0 :: nil) j) in Heq by lia;
        replace (n - 1 - i) with j by lia;
        exact Heq
    end.
  - match goal with
    | Hchecked : forall k : Z, 0 <= k /\ k < i -> _ |- _ =>
        apply Hchecked; lia
    end.
Qed.

Lemma proof_of_p048_is_palindrome_return_wit_1 : p048_is_palindrome_return_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full text_pre (n + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial.
      unfold problem_48_spec, bool_of, palindrome.
      split.
      * intros _ k Hk Hmid.
        match goal with
        | Hlen : Zlength l = n |- _ =>
            rewrite Hlen
        end.
        match goal with
        | Hchecked : forall k : Z, 0 <= k /\ k < i -> _ |- _ =>
            apply Hchecked; lia
        end.
      * intros _.
        reflexivity.
Qed.

Lemma proof_of_p048_is_palindrome_return_wit_2 : p048_is_palindrome_return_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full text_pre (n + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial.
      unfold problem_48_spec, bool_of, palindrome.
      split.
      * intros Hfalse.
        discriminate.
      * intros Hpal.
        specialize (Hpal i).
        assert (Hrange : 0 <= i < Zlength l) by lia.
        assert (Hlt : i < Zlength l - 1 - i) by lia.
        specialize (Hpal Hrange Hlt).
        replace (Zlength l - 1 - i) with j in Hpal by lia.
        assert (Znth i l 0 <> Znth j l 0) as Hneq.
        {
          match goal with
          | Hneq_app : Znth i (app l (0 :: nil)) 0 <>
                       Znth j (app l (0 :: nil)) 0 |- _ =>
              intro Heq;
              apply Hneq_app;
              rewrite (app_Znth1 0 l (0 :: nil) i) by lia;
              rewrite (app_Znth1 0 l (0 :: nil) j) by lia;
              exact Heq
          end.
        }
        exfalso.
        exact (Hneq Hpal).
Qed.

Lemma proof_of_p048_is_palindrome_return_wit_3 : p048_is_palindrome_return_wit_3.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full text_pre (n + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial.
      unfold problem_48_spec, bool_of, palindrome.
      split.
      * intros _ k Hk _.
        exfalso.
        match goal with
        | Hlen : Zlength l = n |- _ =>
            rewrite Hlen in Hk
        end.
        lia.
      * intros _.
        reflexivity.
Qed.

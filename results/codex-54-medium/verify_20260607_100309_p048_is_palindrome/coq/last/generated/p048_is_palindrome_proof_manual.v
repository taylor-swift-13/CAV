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
From SimpleC.EE.verify_20260607_100309_p048_is_palindrome Require Import p048_is_palindrome_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p048_is_palindrome.
From SimpleC.EE.annotated Require Import char_array_strategy_goal.
From SimpleC.EE.annotated Require Import char_array_strategy_proof.
Local Open Scope sac.

Lemma proof_of_p048_is_palindrome_safety_wit_1 : p048_is_palindrome_safety_wit_1.
Proof. pre_process. Qed.

Lemma proof_of_p048_is_palindrome_safety_wit_2 : p048_is_palindrome_safety_wit_2.
Proof. pre_process. Qed.

Lemma proof_of_p048_is_palindrome_safety_wit_3 : p048_is_palindrome_safety_wit_3.
Proof. pre_process. Qed.

Lemma proof_of_p048_is_palindrome_safety_wit_4 : p048_is_palindrome_safety_wit_4.
Proof. pre_process. Qed.

Lemma proof_of_p048_is_palindrome_safety_wit_5 : p048_is_palindrome_safety_wit_5.
Proof. pre_process. Qed.

Lemma proof_of_p048_is_palindrome_safety_wit_6 : p048_is_palindrome_safety_wit_6.
Proof. pre_process. Qed.

Lemma proof_of_p048_is_palindrome_safety_wit_7 : p048_is_palindrome_safety_wit_7.
Proof. pre_process. Qed.

Lemma proof_of_p048_is_palindrome_safety_wit_8 : p048_is_palindrome_safety_wit_8.
Proof. pre_process. Qed.

Lemma proof_of_p048_is_palindrome_safety_wit_9 : p048_is_palindrome_safety_wit_9.
Proof. pre_process. Qed.

Lemma proof_of_p048_is_palindrome_safety_wit_10 : p048_is_palindrome_safety_wit_10.
Proof. pre_process. Qed.

Lemma proof_of_p048_is_palindrome_safety_wit_11 : p048_is_palindrome_safety_wit_11.
Proof. pre_process. Qed.

Lemma proof_of_p048_is_palindrome_entail_wit_1 : p048_is_palindrome_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_p048_is_palindrome_entail_wit_4 : p048_is_palindrome_entail_wit_4.
Proof.
  pre_process.
Qed.

Lemma proof_of_p048_is_palindrome_partial_solve_wit_1_pure : p048_is_palindrome_partial_solve_wit_1_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_p048_is_palindrome_partial_solve_wit_1 : p048_is_palindrome_partial_solve_wit_1.
Proof.
  intros _.
  pre_process.
Qed.

Lemma proof_of_p048_is_palindrome_partial_solve_wit_2 : p048_is_palindrome_partial_solve_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - sep_apply_l_atomic (CharArray.full_split_to_missing_i text_pre i (n + 1) (app l (cons 0 nil)) 0).
    + dump_pre_spatial. lia.
    + cancel.
  - split_pures.
    + dump_pre_spatial. exact H.
    + dump_pre_spatial. exact H0.
    + dump_pre_spatial. exact H1.
    + dump_pre_spatial. exact H2.
    + dump_pre_spatial. exact H5.
    + dump_pre_spatial. exact H6.
    + dump_pre_spatial. exact H7.
    + dump_pre_spatial. exact H8.
    + dump_pre_spatial. exact H9.
    + dump_pre_spatial. exact H10.
    + dump_pre_spatial. exact H11.
Qed.

Lemma proof_of_p048_is_palindrome_partial_solve_wit_3 : p048_is_palindrome_partial_solve_wit_3.
Proof.
  pre_process.
  split_pure_spatial.
  - sep_apply_l_atomic (CharArray.full_split_to_missing_i text_pre j (n + 1) (app l (cons 0 nil)) 0).
    + dump_pre_spatial. lia.
    + cancel.
  - split_pures.
    + dump_pre_spatial. exact H.
    + dump_pre_spatial. exact H0.
    + dump_pre_spatial. exact H1.
    + dump_pre_spatial. exact H2.
    + dump_pre_spatial. exact H5.
    + dump_pre_spatial. exact H6.
    + dump_pre_spatial. exact H7.
    + dump_pre_spatial. exact H8.
    + dump_pre_spatial. exact H9.
    + dump_pre_spatial. exact H10.
    + dump_pre_spatial. exact H11.
Qed.

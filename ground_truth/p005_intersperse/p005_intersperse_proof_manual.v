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
From SimpleC.EE.CAV.ground_truth_p005_intersperse Require Import p005_intersperse_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p005_intersperse.
Local Open Scope sac.

Lemma proof_of_p005_intersperse_entail_wit_1 : p005_intersperse_entail_wit_1.
Proof.
  pre_process.
  prop_apply (IntArray.full_length numbers_pre). Intros.
  rewrite intersperse_list_sublist_one by lia.
  sep_apply (IntArray.seg_single out_pre 0 (Znth 0 l 0)).
  entailer!.
Qed.

Lemma proof_of_p005_intersperse_entail_wit_2 : p005_intersperse_entail_wit_2.
Proof.
  pre_process.
  prop_apply (IntArray.full_length numbers_pre). Intros.
  rewrite intersperse_list_sublist_snoc by lia.
  rewrite <- app_assoc.
  entailer!.
Qed.

Lemma proof_of_p005_intersperse_return_wit_1 : p005_intersperse_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = numbers_size_pre) by lia.
  subst i.
  assert (Hk : k = 2 * numbers_size_pre - 1) by lia.
  subst k.
  prop_apply (IntArray.full_length numbers_pre). Intros.
  assert (Hsl : sublist 0 numbers_size_pre l = l).
  {
    apply sublist_self.
    rewrite Zlength_correct.
    match goal with
    | Hlen : Z.of_nat (Datatypes.length l) = numbers_size_pre |- _ =>
        symmetry; exact Hlen
    end.
  }
  rewrite Hsl.
  Exists (intersperse_list l delimeter_pre).
  rewrite (IntArray.undef_seg_empty out_pre (2 * numbers_size_pre - 1)).
  sep_apply (IntArray.seg_to_full out_pre 0 (2 * numbers_size_pre - 1)).
  replace (out_pre + 0 * sizeof (INT)) with out_pre by lia.
  replace (2 * numbers_size_pre - 1 - 0) with (2 * numbers_size_pre - 1) by lia.
  entailer!.
  rewrite intersperse_list_length.
  - rewrite H2. lia.
  - intro Hnil.
    subst l.
    rewrite Zlength_nil in H2.
    lia.
Qed.

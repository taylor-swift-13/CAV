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
From SimpleC.EE.CAV.verify_20260606_181116_p003_below_zero Require Import p003_below_zero_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_p003_below_zero_safety_wit_3 : p003_below_zero_safety_wit_3.
Proof.
  pre_process.
  prop_apply IntArray.full_Zlength.
  Intros_p Hlen.
  assert (Hseq : num + Znth i l 0 = sum (sublist 0 (i + 1) l)).
  {
    rewrite H5.
    rewrite (sublist_split 0 (i + 1) i l) by lia.
    rewrite sum_app.
    rewrite (sublist_single 0 i l) by lia.
    simpl. lia.
  }
  destruct (H2 i (conj H3 H)) as [Hlo Hhi].
  split_pures.
  - dump_pre_spatial. rewrite Hseq. exact Hhi.
  - dump_pre_spatial. rewrite Hseq. exact Hlo.
Qed.

Lemma proof_of_p003_below_zero_entail_wit_1 : p003_below_zero_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_p003_below_zero_entail_wit_2 : p003_below_zero_entail_wit_2.
Proof.
  pre_process.
  prop_apply IntArray.full_Zlength.
  Intros_p Hlen.
  assert (Hseq : num + Znth i l 0 = sum (sublist 0 (i + 1) l)).
  {
    rewrite H6.
    rewrite (sublist_split 0 (i + 1) i l) by lia.
    rewrite sum_app.
    rewrite (sublist_single 0 i l) by lia.
    simpl. lia.
  }
  split_pure_spatial.
  - cancel (IntArray.full operations_pre operations_size_pre l).
  - split_pures; dump_pre_spatial.
    + exact H1.
    + exact H2.
    + exact H3.
    + lia.
    + lia.
    + exact Hseq.
    + intros k_2 [Hk_lo Hk_hi].
      destruct (Z.eq_dec k_2 i) as [Heq | Hneq].
      * subst k_2. rewrite <- Hseq. lia.
      * apply H7. split; lia.
Qed.

Lemma proof_of_p003_below_zero_return_wit_1 : p003_below_zero_return_wit_1.
Proof.
  pre_process.
  Left.
  split_pure_spatial.
  - cancel (IntArray.full operations_pre operations_size_pre l).
  - split_pures; dump_pre_spatial.
    + lia.
    + intros k [Hlo Hhi].
      apply H6. split.
      * exact Hlo.
      * lia.
Qed.

Lemma proof_of_p003_below_zero_return_wit_2 : p003_below_zero_return_wit_2.
Proof.
  pre_process.
  Right.
  Exists i.
  prop_apply IntArray.full_Zlength.
  Intros_p Hlen.
  assert (Hseq : num + Znth i l 0 = sum (sublist 0 (i + 1) l)).
  {
    rewrite H6.
    rewrite (sublist_split 0 (i + 1) i l) by lia.
    rewrite sum_app.
    rewrite (sublist_single 0 i l) by lia.
    simpl. lia.
  }
  split_pure_spatial.
  - cancel (IntArray.full operations_pre operations_size_pre l).
  - split_pures; dump_pre_spatial.
    + lia.
    + exact H4.
    + exact H0.
    + rewrite <- Hseq. exact H.
Qed.

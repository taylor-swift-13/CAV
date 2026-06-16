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
From SimpleC.EE.CAV.verify_20260606_200943_p003_below_zero Require Import p003_below_zero_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_p003_below_zero_safety_wit_3 : p003_below_zero_safety_wit_3.
Proof.
  unfold p003_below_zero_safety_wit_3.
  pre_process.
  prop_apply IntArray.full_Zlength.
  entailer!.
  all:
    assert (sum (sublist 0 (i + 1) l) = num + Znth i l 0) as Hsum;
    [ rewrite H2;
      rewrite (sublist_split 0 (i + 1) i l) by lia;
      rewrite sum_app;
      rewrite (sublist_single 0 i l) by lia;
      simpl; lia
    | specialize (H9 i (conj H0 H));
      rewrite Hsum in H9;
      lia ].
Qed.

Lemma proof_of_p003_below_zero_entail_wit_1 : p003_below_zero_entail_wit_1.
Proof. pre_process. Qed.

Lemma proof_of_p003_below_zero_entail_wit_2 : p003_below_zero_entail_wit_2.
Proof.
  unfold p003_below_zero_entail_wit_2.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full operations_pre operations_size_pre l).
  - prop_apply IntArray.full_Zlength.
    entailer!.
    rewrite H2.
    rewrite (sublist_split 0 (i + 1) i l) by lia.
    rewrite sum_app.
    rewrite (sublist_single 0 i l) by lia.
    simpl. lia.
Qed.

Lemma proof_of_p003_below_zero_entail_wit_3 : p003_below_zero_entail_wit_3.
Proof.
  unfold p003_below_zero_entail_wit_3.
  pre_process.
  split_pure_spatial.
  - cancel (IntArray.full operations_pre operations_size_pre l).
  - prop_apply IntArray.full_Zlength.
    entailer!.
    intros k [Hk0 Hk].
    destruct (Z_lt_ge_dec k i) as [Hki | Hki].
    + apply H5; lia.
    + replace k with i by lia.
      rewrite <- H2.
      lia.
Qed.

Lemma proof_of_p003_below_zero_return_wit_1 : p003_below_zero_return_wit_1.
Proof.
  unfold p003_below_zero_return_wit_1.
  pre_process.
  unfold naive_C_Rules.derivable1.
  intros m Hm.
  left.
  unfold naive_C_Rules.andp, naive_C_Rules.coq_prop.
  repeat split; try trivial; try (intros k Hk; assert (k < i) by lia; apply H5; lia); try exact Hm.
Qed.

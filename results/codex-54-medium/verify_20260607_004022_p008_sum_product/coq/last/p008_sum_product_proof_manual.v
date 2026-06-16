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
From SimpleC.EE Require Import p008_sum_product_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p008_sum_product.
Local Open Scope sac.

Lemma proof_of_p008_sum_product_safety_wit_5 : p008_sum_product_safety_wit_5.
Proof.
  unfold p008_sum_product_safety_wit_5.
  intros. Intros.
  prop_apply IntArray.full_Zlength.
  Intros.
  assert (Hsum_next : sum + Znth i lv 0 = prefix_sum lv (i + 1)).
  {
    subst sum.
    unfold prefix_sum.
    rewrite (sublist_split 0%Z (i + 1) i lv) by lia.
    rewrite List.fold_left_app.
    rewrite (sublist_single 0%Z i lv) by lia.
    simpl.
    lia.
  }
  specialize (H11 (i + 1)).
  assert (INT_MIN <= sum + Znth i lv 0 <= INT_MAX).
  {
    rewrite Hsum_next.
    destruct H11 as [[Hsum_lo Hsum_hi] _].
    - lia.
    - lia.
  }
  entailer!.
Qed.

Lemma proof_of_p008_sum_product_safety_wit_6 : p008_sum_product_safety_wit_6.
Proof.
  unfold p008_sum_product_safety_wit_6.
  intros. Intros.
  prop_apply IntArray.full_Zlength.
  Intros.
  assert (Hprod_next : product * Znth i lv 0 = prefix_product lv (i + 1)).
  {
    subst product.
    unfold prefix_product.
    rewrite (sublist_split 0%Z (i + 1) i lv) by lia.
    rewrite List.fold_left_app.
    rewrite (sublist_single 0%Z i lv) by lia.
    simpl.
    ring.
  }
  specialize (H11 (i + 1)).
  assert (INT_MIN <= product * Znth i lv 0 <= INT_MAX).
  {
    rewrite Hprod_next.
    destruct H11 as [_ [Hprod_lo Hprod_hi]].
    - lia.
    - lia.
  }
  entailer!.
Qed.

Lemma proof_of_p008_sum_product_entail_wit_1 : p008_sum_product_entail_wit_1.
Proof.
  unfold p008_sum_product_entail_wit_1.
  intros. Intros.
  entailer!.
  subst.
  cancel.
Qed.

Lemma proof_of_p008_sum_product_entail_wit_2 : p008_sum_product_entail_wit_2.
Proof.
  unfold p008_sum_product_entail_wit_2.
  intros. Intros.
  prop_apply IntArray.full_Zlength.
  Intros.
  assert (Hsum_next : sum + Znth i lv 0 = prefix_sum lv (i + 1)).
  {
    subst sum.
    unfold prefix_sum.
    rewrite (sublist_split 0%Z (i + 1) i lv) by lia.
    rewrite List.fold_left_app.
    rewrite (sublist_single 0%Z i lv) by lia.
    simpl.
    lia.
  }
  assert (Hprod_next : product * Znth i lv 0 = prefix_product lv (i + 1)).
  {
    subst product.
    unfold prefix_product.
    rewrite (sublist_split 0%Z (i + 1) i lv) by lia.
    rewrite List.fold_left_app.
    rewrite (sublist_single 0%Z i lv) by lia.
    simpl.
    ring.
  }
  entailer!; try lia; eauto.
Qed.

Lemma proof_of_p008_sum_product_return_wit_1 : p008_sum_product_return_wit_1.
Proof.
  unfold p008_sum_product_return_wit_1.
  intros. Intros.
  Exists sum product.
  prop_apply IntArray.full_length.
  entailer!.
  - subst numbers_pre numbers_size_pre.
    cancel (IntArray.full numbers0 numbers_size0 lv).
    rewrite (logic_equiv_sepcon_comm
               ((retval + 1 * sizeof (INT)) # Int |-> product)
               ((retval + 0 * sizeof (INT)) # Int |-> sum)).
    eapply derivable1_trans with
      (IntArray.seg retval 0 1 (sum :: nil) **
       IntArray.seg retval 1 2 (product :: nil)).
    + {
        apply derivable1_sepcon_mono.
        - apply IntArray.seg_single.
        - apply IntArray.seg_single.
      }
    + {
        eapply derivable1_trans with
          (IntArray.full (retval + 0 * sizeof (INT)) (2 - 0)
             ((sum :: nil) ++ (product :: nil))).
        - {
            apply IntArray.seg_merge_to_full; lia.
          }
        - {
            simpl.
            replace (retval + 0) with retval by lia.
            apply derivable1_refl.
          }
      }
  - unfold problem_8_spec.
    split.
    + replace i with numbers_size0 in * by lia.
      replace numbers_size0 with numbers_size_pre in * by lia.
      subst sum.
      unfold prefix_sum, sublist.
      simpl.
      rewrite firstn_all2 by lia.
      reflexivity.
    + replace i with numbers_size0 in * by lia.
      replace numbers_size0 with numbers_size_pre in * by lia.
      subst product.
      unfold prefix_product, sublist.
      simpl.
      rewrite firstn_all2 by lia.
      reflexivity.
Qed.

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
From SimpleC.EE.CAV.verify_20260607_033329_p011_string_xor Require Import p011_string_xor_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_p011_string_xor_entail_wit_1_1 : p011_string_xor_entail_wit_1_1.
Proof.
  pre_process.
  subst.
  prop_apply (CharArray.full_Zlength retval (Zlength l2 + 1) l).
  Intros_p Hlen.
  destruct (Z_lt_ge_dec (Zlength l2) (Zlength l1)) as [Hlt | Hge].
  - right.
    exists l.
    split.
    + repeat split.
      * change (0 <= 0). lia.
      * change (0 <= Zlength l2). lia.
      * change (0 <= Zlength l1). lia.
      * change (Zlength l1 < 2147483647). lia.
      * change (0 <= Zlength l2). lia.
      * change (Zlength l2 < 2147483647). lia.
      * change (Zlength l2 < Zlength l1). exact Hlt.
      * exact Hlen.
      * change (forall k : Z,
          0 <= k < 0 ->
          Znth k l1 0 = Znth k l2 0 /\ Znth k l 0 = 48 \/
          Znth k l1 0 <> Znth k l2 0 /\ Znth k l 0 = 49).
        intros k Hk. lia.
      * change (forall k_2 : Z, 0 <= k_2 < 0 -> Znth k_2 l 0 <> 0).
        intros k Hk. lia.
    + assert (Hsp :
        CharArray.full retval (Zlength l2 + 1) l **
        (&( "n") # Int |-> Zlength l2 **
         (CharArray.full b_pre (Zlength l2 + 1) (l2 ++ 0 :: nil) **
          (&( "n2") # Int |-> Zlength l2 **
           (CharArray.full a_pre (Zlength l1 + 1) (l1 ++ 0 :: nil) **
            &( "n1") # Int |-> Zlength l1))))
        |--
        &( "n") # Int |-> Zlength l2 **
        &( "n1") # Int |-> Zlength l1 **
        &( "n2") # Int |-> Zlength l2 **
        CharArray.full a_pre (Zlength l1 + 1) (l1 ++ 0 :: nil) **
        CharArray.full b_pre (Zlength l2 + 1) (l2 ++ 0 :: nil) **
        CharArray.full retval (Zlength l2 + 1) l) by (cancel; cancel; cancel).
      exact (Hsp _ H0).
  - assert (Heq : Zlength l1 = Zlength l2) by lia.
    left.
    exists l.
    rewrite Heq.
    rewrite Heq in H0.
    split.
    + repeat split.
      * change (0 <= 0). lia.
      * change (0 <= Zlength l2). lia.
      * change (0 <= Zlength l2). lia.
      * change (Zlength l2 < 2147483647). lia.
      * change (0 <= Zlength l2). lia.
      * change (Zlength l2 < 2147483647). lia.
      * change (Zlength l2 <= Zlength l2). lia.
      * exact Hlen.
      * change (forall k : Z,
          0 <= k < 0 ->
          Znth k l1 0 = Znth k l2 0 /\ Znth k l 0 = 48 \/
          Znth k l1 0 <> Znth k l2 0 /\ Znth k l 0 = 49).
        intros k Hk. lia.
      * change (forall k_2 : Z, 0 <= k_2 < 0 -> Znth k_2 l 0 <> 0).
        intros k Hk. lia.
    + assert (Hsp :
        CharArray.full retval (Zlength l2 + 1) l **
        (&( "n") # Int |-> Zlength l2 **
         (CharArray.full b_pre (Zlength l2 + 1) (l2 ++ 0 :: nil) **
          (&( "n2") # Int |-> Zlength l2 **
           (CharArray.full a_pre (Zlength l2 + 1) (l1 ++ 0 :: nil) **
            &( "n1") # Int |-> Zlength l2))))
        |--
        &( "n") # Int |-> Zlength l2 **
        &( "n1") # Int |-> Zlength l2 **
        &( "n2") # Int |-> Zlength l2 **
        CharArray.full a_pre (Zlength l2 + 1) (l1 ++ 0 :: nil) **
        CharArray.full b_pre (Zlength l2 + 1) (l2 ++ 0 :: nil) **
        CharArray.full retval (Zlength l2 + 1) l) by (cancel; cancel; cancel).
      exact (Hsp _ H0).
Qed.

Lemma proof_of_p011_string_xor_entail_wit_1_2 : p011_string_xor_entail_wit_1_2.
Proof.
  pre_process.
  subst.
  prop_apply (CharArray.full_Zlength retval (Zlength l1 + 1) l).
  Intros_p Hlen.
  left.
  exists l.
  split.
  - repeat split.
    * change (0 <= 0). lia.
    * change (0 <= Zlength l1). lia.
    * change (0 <= Zlength l1). lia.
    * change (Zlength l1 < 2147483647). lia.
    * change (0 <= Zlength l2). lia.
    * change (Zlength l2 < 2147483647). lia.
    * change (Zlength l1 <= Zlength l2). lia.
    * exact Hlen.
    * change (forall k : Z,
        0 <= k < 0 ->
        Znth k l1 0 = Znth k l2 0 /\ Znth k l 0 = 48 \/
        Znth k l1 0 <> Znth k l2 0 /\ Znth k l 0 = 49).
      intros k Hk. lia.
    * change (forall k_2 : Z, 0 <= k_2 < 0 -> Znth k_2 l 0 <> 0).
      intros k Hk. lia.
  - assert (Hsp :
      CharArray.full retval (Zlength l1 + 1) l **
      (&( "n") # Int |-> Zlength l1 **
       (CharArray.full b_pre (Zlength l2 + 1) (l2 ++ 0 :: nil) **
        (&( "n2") # Int |-> Zlength l2 **
         (CharArray.full a_pre (Zlength l1 + 1) (l1 ++ 0 :: nil) **
          &( "n1") # Int |-> Zlength l1))))
      |--
      &( "n") # Int |-> Zlength l1 **
      &( "n1") # Int |-> Zlength l1 **
      &( "n2") # Int |-> Zlength l2 **
      CharArray.full a_pre (Zlength l1 + 1) (l1 ++ 0 :: nil) **
      CharArray.full b_pre (Zlength l2 + 1) (l2 ++ 0 :: nil) **
      CharArray.full retval (Zlength l1 + 1) l) by (cancel; cancel; cancel).
    exact (Hsp _ H0).
Qed.

Lemma proof_of_p011_string_xor_entail_wit_2_1 : p011_string_xor_entail_wit_2_1.
Proof.
  pre_process.
  left.
  exists (replace_Znth i 48 buf_l_2).
  split.
  - repeat split.
    + rewrite Zlength_replace_Znth. lia.
    + intros k Hk.
      destruct Hk as [Hk0 Hki].
      destruct (Z.eq_dec k i) as [-> | Hneq].
      * left. split.
        -- dump_pre_pure. lia.
        -- rewrite Znth_replace_Znth_Same by lia. lia.
      * specialize (H13 k ltac:(lia)).
        destruct H13 as [[Heq Hout] | [Hneq' Hout]].
        -- left. split.
           ++ exact Heq.
           ++ rewrite Znth_replace_Znth_Diff by lia. exact Hout.
        -- right. split.
           ++ exact Hneq'.
           ++ rewrite Znth_replace_Znth_Diff by lia. exact Hout.
    + intros k Hk.
      destruct Hk as [Hk0 Hki].
      destruct (Z.eq_dec k i) as [-> | Hneq].
      * rewrite Znth_replace_Znth_Same by lia. lia.
      * specialize (H14 k ltac:(lia)).
        rewrite Znth_replace_Znth_Diff by lia.
        exact H14.
  - assert (Hsp :
      CharArray.full output (na + 1) (replace_Znth i 48 buf_l_2) **
      (CharArray.full b (nb + 1) (l2 ++ 0 :: nil) **
       (CharArray.full a (na + 1) (l1 ++ 0 :: nil) **
        &( "n") # Int |-> na))
      |--
      &( "n") # Int |-> na **
      CharArray.full a (na + 1) (l1 ++ 0 :: nil) **
      CharArray.full b (nb + 1) (l2 ++ 0 :: nil) **
      CharArray.full output (na + 1) (replace_Znth i 48 buf_l_2)) by (cancel; cancel; cancel).
    exact (Hsp _ H13).
Qed. 

Lemma proof_of_p011_string_xor_entail_wit_2_2 : p011_string_xor_entail_wit_2_2.
Proof.
  pre_process.
  right.
  exists (replace_Znth i 48 buf_l_2).
  split.
  - repeat split.
    + rewrite Zlength_replace_Znth. lia.
    + intros k Hk.
      destruct Hk as [Hk0 Hki].
      destruct (Z.eq_dec k i) as [-> | Hneq].
      * left. split.
        -- dump_pre_pure. lia.
        -- rewrite Znth_replace_Znth_Same by lia. lia.
      * specialize (H13 k ltac:(lia)).
        destruct H13 as [[Heq Hout] | [Hneq' Hout]].
        -- left. split.
           ++ exact Heq.
           ++ rewrite Znth_replace_Znth_Diff by lia. exact Hout.
        -- right. split.
           ++ exact Hneq'.
           ++ rewrite Znth_replace_Znth_Diff by lia. exact Hout.
    + intros k Hk.
      destruct Hk as [Hk0 Hki].
      destruct (Z.eq_dec k i) as [-> | Hneq].
      * rewrite Znth_replace_Znth_Same by lia. lia.
      * specialize (H14 k ltac:(lia)).
        rewrite Znth_replace_Znth_Diff by lia.
        exact H14.
  - assert (Hsp :
      CharArray.full output (nb + 1) (replace_Znth i 48 buf_l_2) **
      (CharArray.full b (nb + 1) (l2 ++ 0 :: nil) **
       (CharArray.full a (na + 1) (l1 ++ 0 :: nil) **
        &( "n") # Int |-> nb))
      |--
      &( "n") # Int |-> nb **
      CharArray.full a (na + 1) (l1 ++ 0 :: nil) **
      CharArray.full b (nb + 1) (l2 ++ 0 :: nil) **
      CharArray.full output (nb + 1) (replace_Znth i 48 buf_l_2)) by (cancel; cancel; cancel).
    exact (Hsp _ H13).
Qed. 

Lemma proof_of_p011_string_xor_entail_wit_2_3 : p011_string_xor_entail_wit_2_3.
Proof.
  pre_process.
  left.
  exists (replace_Znth i 49 buf_l_2).
  split.
  - repeat split.
    + rewrite Zlength_replace_Znth. lia.
    + intros k Hk.
      destruct Hk as [Hk0 Hki].
      destruct (Z.eq_dec k i) as [-> | Hneq].
      * right. split.
        -- dump_pre_pure. lia.
        -- rewrite Znth_replace_Znth_Same by lia. lia.
      * specialize (H13 k ltac:(lia)).
        destruct H13 as [[Heq Hout] | [Hneq' Hout]].
        -- left. split.
           ++ exact Heq.
           ++ rewrite Znth_replace_Znth_Diff by lia. exact Hout.
        -- right. split.
           ++ exact Hneq'.
           ++ rewrite Znth_replace_Znth_Diff by lia. exact Hout.
    + intros k Hk.
      destruct Hk as [Hk0 Hki].
      destruct (Z.eq_dec k i) as [-> | Hneq].
      * rewrite Znth_replace_Znth_Same by lia. lia.
      * specialize (H14 k ltac:(lia)).
        rewrite Znth_replace_Znth_Diff by lia.
        exact H14.
  - assert (Hsp :
      CharArray.full output (na + 1) (replace_Znth i 49 buf_l_2) **
      (CharArray.full b (nb + 1) (l2 ++ 0 :: nil) **
       (CharArray.full a (na + 1) (l1 ++ 0 :: nil) **
        &( "n") # Int |-> na))
      |--
      &( "n") # Int |-> na **
      CharArray.full a (na + 1) (l1 ++ 0 :: nil) **
      CharArray.full b (nb + 1) (l2 ++ 0 :: nil) **
      CharArray.full output (na + 1) (replace_Znth i 49 buf_l_2)) by (cancel; cancel; cancel).
    exact (Hsp _ H13).
Qed. 

Lemma proof_of_p011_string_xor_entail_wit_2_4 : p011_string_xor_entail_wit_2_4.
Proof.
  pre_process.
  right.
  exists (replace_Znth i 49 buf_l_2).
  split.
  - repeat split.
    + rewrite Zlength_replace_Znth. lia.
    + intros k Hk.
      destruct Hk as [Hk0 Hki].
      destruct (Z.eq_dec k i) as [-> | Hneq].
      * right. split.
        -- dump_pre_pure. lia.
        -- rewrite Znth_replace_Znth_Same by lia. lia.
      * specialize (H13 k ltac:(lia)).
        destruct H13 as [[Heq Hout] | [Hneq' Hout]].
        -- left. split.
           ++ exact Heq.
           ++ rewrite Znth_replace_Znth_Diff by lia. exact Hout.
        -- right. split.
           ++ exact Hneq'.
           ++ rewrite Znth_replace_Znth_Diff by lia. exact Hout.
    + intros k Hk.
      destruct Hk as [Hk0 Hki].
      destruct (Z.eq_dec k i) as [-> | Hneq].
      * rewrite Znth_replace_Znth_Same by lia. lia.
      * specialize (H14 k ltac:(lia)).
        rewrite Znth_replace_Znth_Diff by lia.
        exact H14.
  - assert (Hsp :
      CharArray.full output (nb + 1) (replace_Znth i 49 buf_l_2) **
      (CharArray.full b (nb + 1) (l2 ++ 0 :: nil) **
       (CharArray.full a (na + 1) (l1 ++ 0 :: nil) **
        &( "n") # Int |-> nb))
      |--
      &( "n") # Int |-> nb **
      CharArray.full a (na + 1) (l1 ++ 0 :: nil) **
      CharArray.full b (nb + 1) (l2 ++ 0 :: nil) **
      CharArray.full output (nb + 1) (replace_Znth i 49 buf_l_2)) by (cancel; cancel; cancel).
    exact (Hsp _ H13).
Qed. 

Lemma proof_of_p011_string_xor_entail_wit_3_1 : p011_string_xor_entail_wit_3_1.
Proof.
  pre_process.
  left.
  exists buf_l_2.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia.
Qed.

Lemma proof_of_p011_string_xor_entail_wit_3_2 : p011_string_xor_entail_wit_3_2.
Proof.
  pre_process.
  right.
  exists buf_l_2.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia.
Qed.

Lemma proof_of_p011_string_xor_return_wit_1 : p011_string_xor_return_wit_1.
Proof.
  pre_process.
  right.
  Exists (sublist 0 na buf_l), na.
  split_pure_spatial.
  - cancel.
    replace (replace_Znth na 0 buf_l) with ((sublist 0 na buf_l) ++ 0 :: nil).
    + cancel.
    + rewrite <- H1 at 1.
      rewrite replace_Znth_app_r by lia.
      rewrite replace_Znth_nothing by lia.
      replace (na - na) with 0 by lia.
      simpl.
      rewrite Z.sub_0_r.
      reflexivity.
  - split_pures.
    + dump_pre_pure. lia.
    + dump_pre_pure. lia.
    + intros k Hk. apply H11. lia.
    + intros k Hk. apply H12. lia.
    + intros k Hk.
      rewrite Znth_sublist by lia.
      apply H12. lia.
    + dump_pre_pure. lia.
    + dump_pre_pure. lia.
    + intros k Hk.
      rewrite Znth_sublist by lia.
      apply H11. lia.
Qed. 

Lemma proof_of_p011_string_xor_return_wit_2 : p011_string_xor_return_wit_2.
Proof.
  pre_process.
  left.
  Exists (sublist 0 nb buf_l), nb.
  split_pure_spatial.
  - cancel.
    replace (replace_Znth nb 0 buf_l) with ((sublist 0 nb buf_l) ++ 0 :: nil).
    + cancel.
    + rewrite <- H1 at 1.
      rewrite replace_Znth_app_r by lia.
      rewrite replace_Znth_nothing by lia.
      replace (nb - nb) with 0 by lia.
      simpl.
      rewrite Z.sub_0_r.
      reflexivity.
  - split_pures.
    + intros k Hk. apply H11. lia.
    + intros k Hk. apply H12. lia.
    + intros k Hk.
      rewrite Znth_sublist by lia.
      apply H12. lia.
    + dump_pre_pure. lia.
    + dump_pre_pure. lia.
    + intros k Hk.
      rewrite Znth_sublist by lia.
      apply H11. lia.
Qed. 

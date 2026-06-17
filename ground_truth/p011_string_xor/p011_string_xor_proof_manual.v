Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p011_string_xor Require Import p011_string_xor_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Ltac split_empty_output out n l :=
  sep_apply (CharArray.full_split_to_full out 0 (n + 1) l);
  [ | lia ];
  rewrite Zsublist_nil by lia;
  rewrite (CharArray.full_empty out 0);
  entailer!;
  replace (out + 0 * sizeof(CHAR)) with out by lia;
  replace (n + 1 - 0) with (n + 1) by lia;
  sep_apply CharArray.full_to_seg;
  sep_apply CharArray.seg_to_undef_seg.

Ltac solve_xor_prefix_eq i out_l_2 l1 l2 :=
  intros k Hk;
  destruct (Z_lt_ge_dec k i) as [Hlt | Hge];
  [ rewrite app_Znth1 by lia;
    match goal with
    | Hprev : forall q : Z,
        0 <= q < i ->
        ((Znth q _ 0 = Znth q _ 0 /\ Znth q out_l_2 0 = 48) \/
         (Znth q _ 0 <> Znth q _ 0 /\ Znth q out_l_2 0 = 49)) |- _ =>
        apply Hprev; lia
    end
  | assert (k = i) by lia;
    subst k;
    rewrite app_Znth2 by lia;
    replace (i - Zlength out_l_2) with 0 by lia;
    rewrite Znth0_cons;
    match goal with
    | Heq : Znth i (app l1 (cons 0 nil)) 0 =
             Znth i (app l2 (cons 0 nil)) 0 |- _ =>
        rewrite app_Znth1 in Heq by lia;
        rewrite app_Znth1 in Heq by lia;
        left; split; [exact Heq | reflexivity]
    end ].

Ltac solve_xor_prefix_neq i out_l_2 l1 l2 :=
  intros k Hk;
  destruct (Z_lt_ge_dec k i) as [Hlt | Hge];
  [ rewrite app_Znth1 by lia;
    match goal with
    | Hprev : forall q : Z,
        0 <= q < i ->
        ((Znth q _ 0 = Znth q _ 0 /\ Znth q out_l_2 0 = 48) \/
         (Znth q _ 0 <> Znth q _ 0 /\ Znth q out_l_2 0 = 49)) |- _ =>
        apply Hprev; lia
    end
  | assert (k = i) by lia;
    subst k;
    rewrite app_Znth2 by lia;
    replace (i - Zlength out_l_2) with 0 by lia;
    rewrite Znth0_cons;
    match goal with
    | Hneq : Znth i (app l1 (cons 0 nil)) 0 <>
              Znth i (app l2 (cons 0 nil)) 0 |- _ =>
        right; split;
        [ let Heq := fresh "Heq" in
          intro Heq;
          apply Hneq;
          repeat rewrite app_Znth1 by lia;
          exact Heq
        | reflexivity ]
    end ].

Lemma proof_of_p011_string_xor_entail_wit_2_1 : p011_string_xor_entail_wit_2_1.
Proof.
  pre_process.
  subst retval_2 retval_3.
  Right.
  Exists (@nil Z).
  split_empty_output retval na l.
  entailer!.
Qed.

Lemma proof_of_p011_string_xor_entail_wit_2_2 : p011_string_xor_entail_wit_2_2.
Proof.
  pre_process.
  subst retval_2 retval_3.
  destruct (Z_lt_ge_dec nb na) as [Hlt | Hge].
  - Left.
    Exists (@nil Z).
    split_empty_output retval nb l.
    entailer!.
  - assert (nb = na) by lia.
    subst nb.
    Right.
    Exists (@nil Z).
    split_empty_output retval (Zlength l2) l.
    replace (Zlength l2) with na by lia.
    entailer!.
Qed.

Lemma proof_of_p011_string_xor_entail_wit_3_1 : p011_string_xor_entail_wit_3_1.
Proof.
  pre_process.
  Left.
  Exists (app out_l_2 (cons 48 nil)).
  entailer!.
  - solve_xor_prefix_eq i out_l_2 l1 l2.
  - rewrite Zlength_app_cons. lia.
Qed.

Lemma proof_of_p011_string_xor_entail_wit_3_2 : p011_string_xor_entail_wit_3_2.
Proof.
  pre_process.
  Right.
  Exists (app out_l_2 (cons 48 nil)).
  entailer!.
  - solve_xor_prefix_eq i out_l_2 l1 l2.
  - rewrite Zlength_app_cons. lia.
Qed.

Lemma proof_of_p011_string_xor_entail_wit_3_3 : p011_string_xor_entail_wit_3_3.
Proof.
  pre_process.
  Left.
  Exists (app out_l_2 (cons 49 nil)).
  entailer!.
  - solve_xor_prefix_neq i out_l_2 l1 l2.
  - rewrite Zlength_app_cons. lia.
Qed.

Lemma proof_of_p011_string_xor_entail_wit_3_4 : p011_string_xor_entail_wit_3_4.
Proof.
  pre_process.
  Right.
  Exists (app out_l_2 (cons 49 nil)).
  entailer!.
  - solve_xor_prefix_neq i out_l_2 l1 l2.
  - rewrite Zlength_app_cons. lia.
Qed.

Ltac solve_output_nonzero out_l :=
  intros k Hk;
  match goal with
  | Hrel : forall q : Z,
      0 <= q < _ ->
      ((Znth q _ 0 = Znth q _ 0 /\ Znth q out_l 0 = 48) \/
       (Znth q _ 0 <> Znth q _ 0 /\ Znth q out_l 0 = 49)) |- _ =>
      specialize (Hrel k ltac:(lia));
      destruct Hrel as [[_ Hout] | [_ Hout]];
      rewrite Hout; lia
  end.

Lemma proof_of_p011_string_xor_return_wit_1 : p011_string_xor_return_wit_1.
Proof.
  pre_process.
  assert (i = na) by lia.
  subst i.
  Right.
  Exists out_l_2 na.
  rewrite (CharArray.undef_seg_empty output (na + 1)).
  match goal with
  | Hlen : Zlength out_l_2 = na |- _ => rewrite Hlen in *
  end.
  entailer!.
  solve_output_nonzero out_l_2.
Qed.

Lemma proof_of_p011_string_xor_return_wit_2 : p011_string_xor_return_wit_2.
Proof.
  pre_process.
  assert (i = nb) by lia.
  subst i.
  Left.
  Exists out_l_2 nb.
  rewrite (CharArray.undef_seg_empty output (nb + 1)).
  match goal with
  | Hlen : Zlength out_l_2 = nb |- _ => rewrite Hlen in *
  end.
  entailer!.
  solve_output_nonzero out_l_2.
Qed.

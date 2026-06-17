(* spec/142 *)
(* def sum_squares(lst):
This function will take a list of integers. For all entries in the list, the function shall square the integer entry if its index is a
multiple of 3 and will cube the integer entry if its index is a multiple of 4 and not a multiple of 3. The function will not
change the entries in the list whose indexes are not a multiple of 3 or 4. The function shall then return the sum of all entries.

Examples:
For lst = [1,2,3] the output should be 6
For lst = [] the output should be 0
For lst = [-1,-5,2,-1,-5] the output should be -126
 *)

Require Import Coq.Lists.List Coq.ZArith.ZArith.
Import ListNotations.

Require Import Coq.ZArith.Zquot.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition transformed_value (i x : Z) : Z :=
  if Z.rem i 3 =? 0 then x * x
  else if Z.rem i 4 =? 0 then x * x * x
  else x.

Fixpoint transformed_sum_from (l : list Z) (start : Z) : Z :=
  match l with
  | nil => 0
  | x :: xs => transformed_value start x + transformed_sum_from xs (start + 1)
  end.

Definition transformed_prefix_sum (i : Z) (l : list Z) : Z :=
  transformed_sum_from (sublist 0 i l) 0.

Definition problem_142_pre (l : list Z) : Prop :=
  True.

Definition problem_142_spec (l : list Z) (out : Z) : Prop :=
  out = transformed_sum_from l 0.

Definition sum_squares_int_range (l : list Z) : Prop :=
  (forall i,
     0 <= i < Zlength l ->
     let x := Znth i l 0 in
     INT_MIN <= x * x <= INT_MAX /\
     INT_MIN <= x * x * x <= INT_MAX /\
     INT_MIN <= transformed_prefix_sum i l + transformed_value i x <= INT_MAX) /\
  (forall i, 0 <= i <= Zlength l -> INT_MIN <= transformed_prefix_sum i l <= INT_MAX).

Lemma transformed_sum_from_app_single : forall xs x start,
  transformed_sum_from (xs ++ x :: nil) start =
  transformed_sum_from xs start + transformed_value (start + Zlength xs) x.
Proof.
  induction xs; intros x start; simpl.
  - change (Zlength (@nil Z)) with 0.
    rewrite Z.add_0_r.
    rewrite Z.add_0_r.
    reflexivity.
  - rewrite IHxs.
    rewrite Zlength_cons.
    replace (Z.succ (Zlength xs)) with (1 + Zlength xs) by lia.
    replace (start + 1 + Zlength xs) with (start + (1 + Zlength xs)) by lia.
    rewrite Z.add_assoc.
    reflexivity.
Qed.

Lemma transformed_prefix_sum_0 : forall l,
  transformed_prefix_sum 0 l = 0.
Proof.
  intros l.
  unfold transformed_prefix_sum, sublist.
  simpl.
  reflexivity.
Qed.

Lemma transformed_prefix_sum_snoc : forall l i,
  0 <= i < Zlength l ->
  transformed_prefix_sum (i + 1) l =
  transformed_prefix_sum i l + transformed_value i (Znth i l 0).
Proof.
  intros l i Hi.
  unfold transformed_prefix_sum.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single 0 i l) by lia.
  rewrite transformed_sum_from_app_single.
  rewrite Zlength_sublist by lia.
  replace (0 + (i - 0)) with i by lia.
  reflexivity.
Qed.

Lemma transformed_prefix_sum_full : forall l,
  transformed_prefix_sum (Zlength l) l = transformed_sum_from l 0.
Proof.
  intros l.
  unfold transformed_prefix_sum.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed.

Lemma problem_142_spec_of_prefix_full : forall l out,
  out = transformed_prefix_sum (Zlength l) l ->
  problem_142_spec l out.
Proof.
  intros l out Hout.
  unfold problem_142_spec.
  rewrite Hout.
  apply transformed_prefix_sum_full.
Qed.

Lemma sum_squares_next_range : forall l i,
  sum_squares_int_range l ->
  0 <= i < Zlength l ->
  INT_MIN <= transformed_prefix_sum i l + transformed_value i (Znth i l 0) <= INT_MAX.
Proof.
  intros l i [Hstep _] Hi.
  pose proof (Hstep i Hi) as [_ [_ Hsum]].
  exact Hsum.
Qed.

Lemma sum_squares_square_range : forall l i,
  sum_squares_int_range l ->
  0 <= i < Zlength l ->
  INT_MIN <= Znth i l 0 * Znth i l 0 <= INT_MAX.
Proof.
  intros l i [Hstep _] Hi.
  pose proof (Hstep i Hi) as [Hsq _].
  exact Hsq.
Qed.

Lemma sum_squares_cube_range : forall l i,
  sum_squares_int_range l ->
  0 <= i < Zlength l ->
  INT_MIN <= Znth i l 0 * Znth i l 0 * Znth i l 0 <= INT_MAX.
Proof.
  intros l i [Hstep _] Hi.
  pose proof (Hstep i Hi) as [_ [Hcube _]].
  exact Hcube.
Qed.

Lemma transformed_value_square : forall i x,
  Z.rem i 3 = 0 ->
  transformed_value i x = x * x.
Proof.
  intros i x H.
  unfold transformed_value.
  apply Z.eqb_eq in H.
  rewrite H.
  reflexivity.
Qed.

Lemma transformed_value_cube : forall i x,
  Z.rem i 3 <> 0 ->
  Z.rem i 4 = 0 ->
  transformed_value i x = x * x * x.
Proof.
  intros i x H3 H4.
  unfold transformed_value.
  apply Z.eqb_neq in H3.
  apply Z.eqb_eq in H4.
  rewrite H3, H4.
  reflexivity.
Qed.

Lemma transformed_value_plain : forall i x,
  Z.rem i 3 <> 0 ->
  Z.rem i 4 <> 0 ->
  transformed_value i x = x.
Proof.
  intros i x H3 H4.
  unfold transformed_value.
  apply Z.eqb_neq in H3.
  apply Z.eqb_neq in H4.
  rewrite H3, H4.
  reflexivity.
Qed.

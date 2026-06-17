(* spec/68 *)
(* def pluck(arr):
Given an array representing a branch of a tree that has non-negative integer nodes
your task is to pluck one of the nodes and return it.
The plucked node should be the node with the smallest even value.
If multiple nodes with the same smallest even value are found return the node that has smallest index.

The plucked node should be returned in a list, [ smalest_value, its index ],
If there are no even values or the given array is empty, return [].

Example 1:
Input: [4,2,3]
Output: [2, 1]
Explanation: 2 has the smallest even value, and 2 has the smallest index.

Example 2:
Input: [1,2,3]
Output: [2, 1]
Explanation: 2 has the smallest even value, and 2 has the smallest index.

Example 3:
Input: []
Output: []

Example 4:
Input: [5, 0, 3, 0, 4, 2]
Output: [0, 1]
Explanation: 0 is the smallest value, but there are two zeros,
so we will choose the first zero, which has the smallest index.

Constraints:
* 1 <= nodes.length <= 10000
* 0 <= node.value
*)
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.


(* pluck 函数的程序规约 *)

Require Import Coq.ZArith.ZArith.
From AUXLib Require Import ListLib.

Local Open Scope Z_scope.

Definition list_nonnegative (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0.

Definition output_Z_to_option (l : list Z) : option (nat * nat) :=
  match l with
  | [] => None
  | value :: index :: [] => Some (Z.to_nat value, Z.to_nat index)
  | _ => None
  end.

Definition problem_68_pre (arr : list Z) : Prop :=
  True.

Definition pluck_update (x i : Z) (best : list Z) : list Z :=
  if Z.eqb (Z.rem x 2) 0 then
    match best with
    | [] => [x; i]
    | value :: _ =>
        if Z.ltb x value then [x; i] else best
    end
  else best.

Fixpoint pluck_scan_from (i : Z) (arr best : list Z) : list Z :=
  match arr with
  | [] => best
  | x :: xs => pluck_scan_from (i + 1) xs (pluck_update x i best)
  end.

Definition pluck_prefix_result (arr : list Z) (i : Z) : list Z :=
  pluck_scan_from 0 (sublist 0 i arr) [].

Definition pluck_loop_state (arr : list Z) (i : Z) (output : list Z) : Prop :=
  0 <= i <= Zlength arr /\
  output = pluck_prefix_result arr i.

Definition pluck_best_spec (base : Z) (processed best : list Z) : Prop :=
  match best with
  | [] =>
      forall x, In x processed -> Z.rem x 2 <> 0
  | value :: index :: [] =>
      exists idx : nat,
        index = base + Z.of_nat idx /\
        nth_error processed idx = Some value /\
        Z.rem value 2 = 0 /\
        (forall x, In x processed -> Z.rem x 2 = 0 -> value <= x) /\
        (forall j : nat, (j < idx)%nat -> nth j processed 0 <> value)
  | _ => False
  end.

Definition problem_68_spec (arr output : list Z) : Prop :=
  list_nonnegative arr /\
  pluck_best_spec 0 arr output.


(* Ground-truth proof helpers. *)
Lemma pluck_scan_from_app : forall l1 l2 i best,
  pluck_scan_from i (l1 ++ l2) best =
  pluck_scan_from (i + Zlength l1) l2 (pluck_scan_from i l1 best).
Proof.
  induction l1 as [|x xs IH]; intros l2 i best; simpl.
  - change (Zlength (@nil Z)) with 0.
    replace (i + 0) with i by lia.
    reflexivity.
  - rewrite IH.
    rewrite Zlength_cons.
    replace (i + Z.succ (Zlength xs)) with (i + 1 + Zlength xs) by lia.
    reflexivity.
Qed.

Lemma pluck_prefix_result_0 : forall arr,
  pluck_loop_state arr 0 [].
Proof.
  intros arr.
  unfold pluck_loop_state, pluck_prefix_result.
  rewrite Zsublist_nil by lia.
  simpl.
  rewrite Zlength_correct.
  split; [lia | reflexivity].
Qed.

Lemma pluck_prefix_result_step : forall arr i,
  0 <= i < Zlength arr ->
  pluck_prefix_result arr (i + 1) =
  pluck_update (Znth i arr 0) i (pluck_prefix_result arr i).
Proof.
  intros arr i Hi.
  destruct Hi as [Hi0 Hilt].
  rewrite Zlength_correct in Hilt.
  unfold pluck_prefix_result.
  assert (Hsplit: sublist 0 (i + 1) arr = sublist 0 i arr ++ sublist i (i + 1) arr).
  { rewrite (sublist_split 0 (i + 1) i arr) by (rewrite ?Zlength_correct; lia).
    reflexivity. }
  rewrite Hsplit.
  rewrite pluck_scan_from_app.
  rewrite Zlength_sublist by (rewrite Zlength_correct; split; lia).
  rewrite (sublist_single 0 i arr) by (rewrite ?Zlength_correct; lia).
  simpl.
  replace (0 + i) with i by lia.
  replace (i - 0) with i by lia.
  reflexivity.
Qed.

Lemma replace_Znth_two : forall a b l,
  Zlength l = 2 ->
  @replace_Znth Z 1 b (@replace_Znth Z 0 a l) = [a; b].
Proof.
  intros a b l Hlen.
  rewrite Zlength_correct in Hlen.
  destruct l as [|x [|y [|z zs]]]; simpl in Hlen; try lia.
  reflexivity.
Qed.

Lemma pluck_loop_state_update_empty : forall arr i output,
  0 <= i < Zlength arr ->
  pluck_loop_state arr i output ->
  output = [] ->
  Z.rem (Znth i arr 0) 2 = 0 ->
  pluck_loop_state arr (i + 1) [Znth i arr 0; i].
Proof.
  intros arr i output Hi [Hrange Hstate] Hout Heven.
  unfold pluck_loop_state.
  split; [lia |].
  rewrite pluck_prefix_result_step by lia.
  rewrite <- Hstate.
  unfold pluck_update.
  apply Z.eqb_eq in Heven.
  rewrite Heven.
  rewrite Hout.
  reflexivity.
Qed.

Lemma pluck_loop_state_update_less : forall arr i output value index,
  0 <= i < Zlength arr ->
  pluck_loop_state arr i output ->
  output = [value; index] ->
  Z.rem (Znth i arr 0) 2 = 0 ->
  Znth i arr 0 < Znth 0 output 0 ->
  pluck_loop_state arr (i + 1) [Znth i arr 0; i].
Proof.
  intros arr i output value index Hi [Hrange Hstate] Hout Heven Hlt.
  unfold pluck_loop_state.
  split; [lia |].
  rewrite pluck_prefix_result_step by lia.
  rewrite <- Hstate.
  unfold pluck_update.
  apply Z.eqb_eq in Heven.
  rewrite Heven.
  rewrite Hout.
  rewrite Hout in Hlt.
  change (Znth 0 [value; index] 0) with value in Hlt.
  simpl in Hlt.
  apply Z.ltb_lt in Hlt.
  rewrite Hlt.
  reflexivity.
Qed.

Lemma pluck_loop_state_skip_odd : forall arr i output,
  0 <= i < Zlength arr ->
  pluck_loop_state arr i output ->
  Z.rem (Znth i arr 0) 2 <> 0 ->
  pluck_loop_state arr (i + 1) output.
Proof.
  intros arr i output Hi [Hrange Hstate] Hodd.
  unfold pluck_loop_state.
  split; [lia |].
  rewrite pluck_prefix_result_step by lia.
  rewrite <- Hstate.
  unfold pluck_update.
  apply Z.eqb_neq in Hodd.
  rewrite Hodd.
  reflexivity.
Qed.

Lemma pluck_loop_state_skip_ge : forall arr i output value index,
  0 <= i < Zlength arr ->
  pluck_loop_state arr i output ->
  output = [value; index] ->
  Z.rem (Znth i arr 0) 2 = 0 ->
  Znth i arr 0 >= Znth 0 output 0 ->
  pluck_loop_state arr (i + 1) output.
Proof.
  intros arr i output value index Hi [Hrange Hstate] Hout Heven Hge.
  unfold pluck_loop_state.
  split; [lia |].
  rewrite pluck_prefix_result_step by lia.
  rewrite <- Hstate.
  unfold pluck_update.
  apply Z.eqb_eq in Heven.
  rewrite Heven.
  rewrite Hout.
  rewrite Hout in Hge.
  change (Znth 0 [value; index] 0) with value in Hge.
  simpl in Hge.
  assert (Hge' : value <= Znth i arr 0) by lia.
  apply Z.ltb_ge in Hge'.
  rewrite Hge'.
  reflexivity.
Qed.


Lemma pluck_best_spec_update : forall base processed best x,
  pluck_best_spec base processed best ->
  pluck_best_spec base (processed ++ [x])
    (pluck_update x (base + Zlength processed) best).
Proof.
  intros base processed best x Hbest.
  unfold pluck_update.
  destruct (Z.eqb (Z.rem x 2) 0) eqn:Heven.
  - apply Z.eqb_eq in Heven.
    destruct best as [|value [|index [|extra rest]]]; simpl in Hbest; try contradiction.
    + simpl.
      exists (length processed).
      repeat split.
      * rewrite Zlength_correct. lia.
      * rewrite nth_error_app2 by lia.
        replace (length processed - length processed)%nat with 0%nat by lia.
        reflexivity.
      * exact Heven.
      * intros y Hy Hy_even.
        apply in_app_or in Hy.
        destruct Hy as [Hy | [Hy | []]].
        -- exfalso. apply (Hbest y Hy Hy_even).
        -- subst y. lia.
      * intros j Hj.
        rewrite app_nth1 by lia.
        intro Hnth.
        apply Hbest with (x := nth j processed 0).
        -- apply nth_In. lia.
        -- rewrite Hnth. exact Heven.
    + destruct (Z.ltb x value) eqn:Hlt.
      * apply Z.ltb_lt in Hlt.
        destruct Hbest as [idx [Hindex [Hnth [Hvalue_even [Hmin Hfirst]]]]].
        simpl.
        exists (length processed).
        repeat split.
        -- rewrite Zlength_correct. lia.
        -- rewrite nth_error_app2 by lia.
           replace (length processed - length processed)%nat with 0%nat by lia.
           reflexivity.
        -- exact Heven.
        -- intros y Hy Hy_even.
           apply in_app_or in Hy.
           destruct Hy as [Hy | [Hy | []]].
           ++ specialize (Hmin y Hy Hy_even). lia.
           ++ subst y. lia.
        -- intros j Hj.
           rewrite app_nth1 by lia.
           intro Hnth_j.
           destruct (Z.eq_dec (Z.rem (nth j processed 0) 2) 0) as [Hj_even | Hj_odd].
           ++ assert (Hin_j : In (nth j processed 0) processed).
              { apply nth_In. exact Hj. }
              specialize (Hmin (nth j processed 0) Hin_j Hj_even).
              lia.
           ++ rewrite Hnth_j in Hj_odd. contradiction.
      * apply Z.ltb_ge in Hlt.
        destruct Hbest as [idx [Hindex [Hnth [Hvalue_even [Hmin Hfirst]]]]].
        simpl.
        exists idx.
        repeat split.
        -- exact Hindex.
        -- rewrite nth_error_app1; [exact Hnth |].
           apply nth_error_Some.
           rewrite Hnth. discriminate.
        -- exact Hvalue_even.
        -- intros y Hy Hy_even.
           apply in_app_or in Hy.
           destruct Hy as [Hy | [Hy | []]].
           ++ apply Hmin; auto.
           ++ subst y. lia.
        -- intros j Hj.
           rewrite app_nth1.
           ++ apply Hfirst. exact Hj.
           ++ apply nth_error_Some.
              destruct (nth_error processed j) eqn:Hnth_j; [discriminate |].
              assert (Hj_len : (length processed <= j)%nat).
              { apply nth_error_None. exact Hnth_j. }
              assert (Hidx_len : (idx < length processed)%nat).
              { apply nth_error_Some. rewrite Hnth. discriminate. }
              lia.
  - apply Z.eqb_neq in Heven.
    destruct best as [|value [|index [|extra rest]]]; simpl in Hbest; try contradiction.
    + simpl.
      intros y Hy.
      apply in_app_or in Hy.
      destruct Hy as [Hy | [Hy | []]]; subst; auto.
    + destruct Hbest as [idx [Hindex [Hnth [Hvalue_even [Hmin Hfirst]]]]].
      simpl.
      exists idx.
      repeat split.
      * exact Hindex.
      * rewrite nth_error_app1; [exact Hnth |].
        apply nth_error_Some.
        rewrite Hnth. discriminate.
      * exact Hvalue_even.
      * intros y Hy Hy_even.
        apply in_app_or in Hy.
        destruct Hy as [Hy | [Hy | []]].
        -- apply Hmin; auto.
        -- subst y. contradiction.
      * intros j Hj.
        rewrite app_nth1.
        -- apply Hfirst. exact Hj.
        -- apply nth_error_Some.
           destruct (nth_error processed j) eqn:Hnth_j; [discriminate |].
           assert (Hj_len : (length processed <= j)%nat).
           { apply nth_error_None. exact Hnth_j. }
           assert (Hidx_len : (idx < length processed)%nat).
           { apply nth_error_Some. rewrite Hnth. discriminate. }
           lia.
Qed.

Lemma pluck_scan_from_best_spec : forall rest base processed best,
  pluck_best_spec base processed best ->
  pluck_best_spec base (processed ++ rest)
    (pluck_scan_from (base + Zlength processed) rest best).
Proof.
  induction rest as [|x xs IH]; intros base processed best Hbest; simpl.
  - rewrite app_nil_r. exact Hbest.
  - replace (base + Zlength processed + 1)
      with (base + Zlength (processed ++ [x])) by
        (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    replace (processed ++ x :: xs) with ((processed ++ [x]) ++ xs)
      by (rewrite <- app_assoc; reflexivity).
    apply IH.
    apply pluck_best_spec_update.
    exact Hbest.
Qed.

Lemma pluck_prefix_result_best_spec : forall arr,
  pluck_best_spec 0 arr (pluck_prefix_result arr (Zlength arr)).
Proof.
  intros arr.
  unfold pluck_prefix_result.
  rewrite (sublist_self arr (Zlength arr)) by lia.
  replace 0 with (0 + Zlength (@nil Z)) by reflexivity.
  change arr with (@nil Z ++ arr) at 1.
  apply pluck_scan_from_best_spec.
  simpl.
  intros x H; contradiction.
Qed.

Lemma pluck_loop_state_full_spec : forall arr i output,
  list_nonnegative arr ->
  i >= Zlength arr ->
  pluck_loop_state arr i output ->
  problem_68_spec arr output.
Proof.
  intros arr i output Hnonneg Hi [Hrange Hstate].
  unfold problem_68_spec.
  split; [exact Hnonneg |].
  replace i with (Zlength arr) in Hstate by lia.
  rewrite Hstate.
  apply pluck_prefix_result_best_spec.
Qed.

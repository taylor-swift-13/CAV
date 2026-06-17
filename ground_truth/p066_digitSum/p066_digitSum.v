(* spec/66 *)
(* def digitSum(s):
Task
Write a function that takes a string as input and returns the sum of the upper characters only'
ASCII codes.

Examples:
digitSum("") => 0
digitSum("abAB") => 131
digitSum("abcCd") => 67
digitSum("helloE") => 69
digitSum("woArBld") => 131
digitSum("aAaaaXa") => 153 *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import string_bridge.
Import ListNotations.

Local Open Scope Z_scope.

Definition is_upper (x : Z) : bool :=
  (Z.leb 65 x) && (Z.leb x 90).

Fixpoint sum_upper_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if is_upper x then x else 0) + sum_upper_list xs
  end.

Definition sum_upper_upto (i : Z) (l : list Z) : Z :=
  sum_upper_list (firstn (Z.to_nat i) l).

Definition problem_66_pre (s : list Z) : Prop :=
  True.

Definition problem_66_spec (s : list Z) (output : Z) : Prop :=
  output = sum_upper_list s.

Definition digit_sum_int_range (s : list Z) : Prop :=
  forall i,
    0 <= i ->
    i < Zlength s ->
    INT_MIN <= sum_upper_upto i s <= INT_MAX /\
    INT_MIN <= sum_upper_upto i s + Znth i s 0 <= INT_MAX.

Lemma sum_upper_upto_0 : forall l,
  sum_upper_upto 0 l = 0.
Proof.
  intros l.
  unfold sum_upper_upto.
  reflexivity.
Qed.

Lemma sum_upper_list_app : forall l1 l2,
  sum_upper_list (l1 ++ l2) =
  sum_upper_list l1 + sum_upper_list l2.
Proof.
  induction l1 as [| x xs IH]; intros l2; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma firstn_succ_snoc : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = List.app (firstn n l) [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.

Lemma firstn_succ_Znth : forall (l : list Z) i,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  List.app (firstn (Z.to_nat i) l) [Znth i l 0].
Proof.
  intros l i H.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc with (d := 0).
  - reflexivity.
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
Qed.

Lemma sum_upper_upto_step_upper : forall i l,
  0 <= i ->
  i < Zlength l ->
  65 <= Znth i l 0 ->
  Znth i l 0 <= 90 ->
  sum_upper_upto (i + 1) l =
  sum_upper_upto i l + Znth i l 0.
Proof.
  intros i l Hi Hlt Hlo Hhi.
  unfold sum_upper_upto.
  rewrite firstn_succ_Znth by lia.
  rewrite sum_upper_list_app.
  simpl.
  unfold is_upper.
  replace (Z.leb 65 (Znth i l 0)) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb (Znth i l 0) 90) with true by (symmetry; apply Z.leb_le; lia).
  simpl. lia.
Qed.

Lemma sum_upper_upto_step_not_upper : forall i l,
  0 <= i ->
  i < Zlength l ->
  (Znth i l 0 < 65 \/ 90 < Znth i l 0) ->
  sum_upper_upto (i + 1) l =
  sum_upper_upto i l.
Proof.
  intros i l Hi Hlt Hnot.
  unfold sum_upper_upto.
  rewrite firstn_succ_Znth by lia.
  rewrite sum_upper_list_app.
  simpl.
  unfold is_upper.
  destruct Hnot as [Hlo | Hhi].
  - replace (Z.leb 65 (Znth i l 0)) with false by (symmetry; apply Z.leb_gt; lia).
    simpl. lia.
  - replace (Z.leb 65 (Znth i l 0)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.leb (Znth i l 0) 90) with false by (symmetry; apply Z.leb_gt; lia).
    simpl. lia.
Qed.

Lemma problem_66_spec_intro : forall s output,
  output = sum_upper_upto (Zlength s) s ->
  problem_66_spec s output.
Proof.
  intros s output Hout.
  unfold problem_66_spec.
  rewrite Hout.
  unfold sum_upper_upto.
  replace (Z.to_nat (Zlength s)) with (List.length s)
    by (rewrite Zlength_correct; lia).
  rewrite firstn_all.
  reflexivity.
Qed.

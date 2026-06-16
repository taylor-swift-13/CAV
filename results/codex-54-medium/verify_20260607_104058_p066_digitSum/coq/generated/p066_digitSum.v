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

Definition ascii_range (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0 < 256.

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

Lemma sum_upper_list_app_single :
  forall prefix x,
    sum_upper_list (prefix ++ [x]) =
    sum_upper_list prefix + (if is_upper x then x else 0).
Proof.
  induction prefix as [|a prefix IH]; intros x; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma firstn_Znth_decomp :
  forall l i,
    0 <= i < Zlength l ->
    firstn (S (Z.to_nat i)) l = firstn (Z.to_nat i) l ++ [Znth i l 0].
Proof.
  intros l i Hi.
  set (n := Z.to_nat i).
  assert (Hnlt : (n < length l)%nat).
  {
    subst n.
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
  }
  pose proof (@nth_error_nth' Z l n 0 Hnlt) as Hnth.
  remember (List.nth n l 0) as x eqn:Hx.
  apply nth_error_split in Hnth.
  destruct Hnth as [l1 [l2 [Hl Hlen]]].
  subst l.
  replace (S n) with (length l1 + 1)%nat by lia.
  replace n with (length l1 + 0)%nat by lia.
  rewrite !firstn_app_2.
  simpl.
  rewrite app_nil_r.
  assert (HZ : Znth i (l1 ++ x :: l2) 0 = x).
  {
    assert (Hi_eq : i = Z.of_nat (length l1)).
    {
      subst n.
      rewrite Hlen.
      rewrite Z2Nat.id by lia.
      reflexivity.
    }
    rewrite Hi_eq.
    rewrite app_Znth2 by (rewrite Zlength_correct; lia).
    simpl.
    replace (Z.of_nat (length l1) - Zlength l1) with 0 by (rewrite Zlength_correct; lia).
    reflexivity.
  }
  rewrite HZ.
  reflexivity.
Qed.

Lemma sum_upper_upto_step_upper :
  forall l i,
    0 <= i < Zlength l ->
    65 <= Znth i l 0 <= 90 ->
    sum_upper_upto (i + 1) l = sum_upper_upto i l + Znth i l 0.
Proof.
  intros l i Hi Hupper.
  unfold sum_upper_upto.
  rewrite Z2Nat.inj_add by lia.
  replace (Z.to_nat 1) with 1%nat by reflexivity.
  rewrite Nat.add_1_r.
  rewrite firstn_Znth_decomp by exact Hi.
  rewrite sum_upper_list_app_single.
  assert (Hupperb : is_upper (Znth i l 0) = true).
  {
    unfold is_upper.
    apply andb_true_intro.
    split; apply Z.leb_le; lia.
  }
  rewrite Hupperb.
  lia.
Qed.

Lemma sum_upper_upto_step_not_upper :
  forall l i,
    0 <= i < Zlength l ->
    Znth i l 0 < 65 \/ Znth i l 0 > 90 ->
    sum_upper_upto (i + 1) l = sum_upper_upto i l.
Proof.
  intros l i Hi Hnot.
  unfold sum_upper_upto.
  rewrite Z2Nat.inj_add by lia.
  replace (Z.to_nat 1) with 1%nat by reflexivity.
  rewrite Nat.add_1_r.
  rewrite firstn_Znth_decomp by exact Hi.
  rewrite sum_upper_list_app_single.
  destruct Hnot as [Hlt | Hgt].
  - assert (Hupperb : is_upper (Znth i l 0) = false).
    {
      unfold is_upper.
      assert (Hleb : (65 <=? Znth i l 0) = false) by (apply Z.leb_gt; lia).
      rewrite Hleb.
      reflexivity.
    }
    rewrite Hupperb. lia.
  - assert (Hupperb : is_upper (Znth i l 0) = false).
    {
      unfold is_upper.
      assert (Hleb : (Znth i l 0 <=? 90) = false) by (apply Z.leb_gt; lia).
      rewrite Hleb.
      destruct (65 <=? Znth i l 0); reflexivity.
    }
    rewrite Hupperb. lia.
Qed.

Lemma sum_upper_upto_length :
  forall l,
    sum_upper_upto (Zlength l) l = sum_upper_list l.
Proof.
  intros l.
  unfold sum_upper_upto.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  rewrite firstn_all.
  reflexivity.
Qed.

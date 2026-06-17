(* spec/121 *)
(* Given a non-empty list of integers, return the sum of all of the odd elements that are in even positions.
Examples
solution([5, 8, 7, 1]) ==> 12
solution([3, 3, 3, 3, 3]) ==> 9
solution([30, 13, 24, 321]) ==>0*)

Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.

Fixpoint sum_odd_in_even_pos_aux (l : list nat) (idx : nat) : nat :=
  match l with
  | [] => 0
  | h::t => (if (Nat.even idx) && negb (Nat.even h) then h else 0) + sum_odd_in_even_pos_aux t (S idx)
  end.

Definition sum_odd_in_even_pos_impl (l : list nat) : nat := sum_odd_in_even_pos_aux l 0.

(* 非空整数列表 *)


Require Import Coq.ZArith.ZArith.
Require Import Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Fixpoint sum_odd_at_even_upto_nat (n : nat) (l : list Z) : Z :=
  match n with
  | O => 0
  | S n' =>
      let s := sum_odd_at_even_upto_nat n' l in
      let i := Z.of_nat n' in
      let x := Znth (2 * i) l 0 in
      if Z.eqb (Z.rem x 2) 1 then s + x else s
  end.

Definition sum_odd_at_even_upto (i : Z) (l : list Z) : Z :=
  sum_odd_at_even_upto_nat (Z.to_nat i) l.

Definition problem_121_pre (lst : list Z) : Prop :=
  lst <> [].

Definition problem_121_spec (lst : list Z) (output : Z) : Prop :=
  output = sum_odd_at_even_upto (Zlength lst) lst.

Definition odd_even_position_add (x : Z) : Z :=
  if Z.eqb (Z.rem x 2) 1 then x else 0.

Fixpoint sum_odd_in_even_positions (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: [] => odd_even_position_add x
  | x :: _ :: rest => odd_even_position_add x + sum_odd_in_even_positions rest
  end.

Fixpoint sum_odd_in_even_positions_nat (l : list nat) : nat :=
  match l with
  | [] => O
  | x :: [] => if Nat.odd x then x else O
  | x :: _ :: rest => (if Nat.odd x then x else O) + sum_odd_in_even_positions_nat rest
  end.

Definition sum_odd_at_even_int_range (lst : list Z) : Prop :=
  forall i,
    0 <= i ->
    2 * i < Zlength lst ->
    INT_MIN <= sum_odd_at_even_upto i lst <= INT_MAX /\
    INT_MIN <= sum_odd_at_even_upto i lst + Znth (2 * i) lst 0 <= INT_MAX.

Lemma sum_odd_at_even_upto_0 : forall l,
  sum_odd_at_even_upto 0 l = 0.
Proof.
  intros l.
  unfold sum_odd_at_even_upto.
  reflexivity.
Qed.

Lemma sum_odd_at_even_upto_step_odd : forall i l,
  0 <= i ->
  Z.rem (Znth (2 * i) l 0) 2 = 1 ->
  sum_odd_at_even_upto (i + 1) l =
  sum_odd_at_even_upto i l + Znth (2 * i) l 0.
Proof.
  intros i l Hi Hodd.
  unfold sum_odd_at_even_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  change (match i with
          | 0 => 0
          | Z.pos y' => Z.pos y'~0
          | Z.neg y' => Z.neg y'~0
          end) with (2 * i).
  destruct (Z.eqb (Z.rem (Znth (2 * i) l 0) 2) 1) eqn:Heq.
  - reflexivity.
  - apply Z.eqb_neq in Heq. congruence.
Qed.

Lemma sum_odd_at_even_upto_step_not_odd : forall i l,
  0 <= i ->
  Z.rem (Znth (2 * i) l 0) 2 <> 1 ->
  sum_odd_at_even_upto (i + 1) l =
  sum_odd_at_even_upto i l.
Proof.
  intros i l Hi Hnot.
  unfold sum_odd_at_even_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  change (match i with
          | 0 => 0
          | Z.pos y' => Z.pos y'~0
          | Z.neg y' => Z.neg y'~0
          end) with (2 * i).
  destruct (Z.eqb (Z.rem (Znth (2 * i) l 0) 2) 1) eqn:Heq.
  - apply Z.eqb_eq in Heq. congruence.
  - reflexivity.
Qed.

Lemma Znth_default_ge_121 : forall (l : list Z) i d,
  Zlength l <= i ->
  Znth i l d = d.
Proof.
  intros l i d Hi.
  unfold Znth.
  apply nth_overflow.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma sum_odd_at_even_upto_step_out : forall i l,
  0 <= i ->
  Zlength l <= 2 * i ->
  sum_odd_at_even_upto (i + 1) l = sum_odd_at_even_upto i l.
Proof.
  intros i l Hi Hout.
  unfold sum_odd_at_even_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  change (match i with
          | 0 => 0
          | Z.pos y' => Z.pos y'~0
          | Z.neg y' => Z.neg y'~0
          end) with (2 * i).
  rewrite Znth_default_ge_121 by lia.
  reflexivity.
Qed.

Lemma sum_odd_at_even_upto_stable : forall i j l,
  0 <= i ->
  i <= j ->
  Zlength l <= 2 * i ->
  sum_odd_at_even_upto j l = sum_odd_at_even_upto i l.
Proof.
  intros i j l Hi Hij Hout.
  assert (Hstable : forall n,
    sum_odd_at_even_upto (i + Z.of_nat n) l = sum_odd_at_even_upto i l).
  {
    induction n.
    - replace (i + Z.of_nat 0) with i by lia.
      reflexivity.
    - replace (i + Z.of_nat (S n)) with ((i + Z.of_nat n) + 1) by lia.
      transitivity (sum_odd_at_even_upto (i + Z.of_nat n) l).
      + apply sum_odd_at_even_upto_step_out.
        * pose proof (Nat2Z.is_nonneg n). lia.
        * pose proof (Nat2Z.is_nonneg n). lia.
      + apply IHn.
  }
  replace j with (i + Z.of_nat (Z.to_nat (j - i))).
  - apply Hstable.
  - rewrite Z2Nat.id by lia.
    lia.
Qed.

Lemma problem_121_spec_of_exit : forall l i s,
  0 <= i ->
  2 * i <= Zlength l + 1 ->
  Zlength l <= 2 * i ->
  s = sum_odd_at_even_upto i l ->
  problem_121_spec l s.
Proof.
  intros l i s Hi Hbound Hexit Hs.
  unfold problem_121_spec.
  subst s.
  symmetry.
  apply sum_odd_at_even_upto_stable.
  - lia.
  - pose proof (Zlength_nonneg l). lia.
  - lia.
Qed.

(* spec/130 *)
(* def tri_nat(n):
"""Everyone knows Fibonacci sequence, it was studied deeply by mathematicians in
the last couple centuries. However, what people don't know is Tribonacci sequence.
Tribonacci sequence is defined by the recurrence:
tri_nat(1) = 3
tri_nat(n) = 1 + n / 2, if n is even.
tri_nat(n) = tri_nat(n - 1) + tri_nat(n - 2) + tri_nat(n + 1), if n is odd.
For example:
tri_nat(2) = 1 + (2 / 2) = 2
tri_nat(4) = 3
tri_nat(3) = tri_nat(2) + tri_nat(1) + tri_nat(4)
= 2 + 3 + 3 = 8
You are given a non-negative integer number n, you have to a return a list of the
first n + 1 numbers of the Tribonacci sequence.
Examples:
tri_nat(3) = [1, 3, 2, 8]
""" *)
Require Import Arith.
Require Import List.
Import ListNotations.

(* 使用Fixpoint来实现Tribonacci序列的计算 *)
Fixpoint tri_nat (n : nat) : nat :=
  match n with
  | 0 => 1
  | 1 => 3
  | S (S k) =>
      if Nat.even n then
        1 + n / 2
      else
        let t_prev := 1 + (n - 1) / 2 in
        let t_next := 1 + (n + 1) / 2 in
        t_prev + tri_nat k + t_next
  end.

(* n 为非负整数（nat 已满足），无额外约束 *)

(* 定义tri函数的程序规约 *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Fixpoint tri_fuel (fuel : nat) (i : Z) : Z :=
  match fuel with
  | O => if Z.eqb i 1 then 3 else 1
  | S fuel' =>
      if Z.eqb i 0 then 1
      else if Z.eqb i 1 then 3
      else if Z.even i then 1 + Z.quot i 2
      else (1 + Z.quot (i - 1) 2) + tri_fuel fuel' (i - 2) +
           (1 + Z.quot (i + 1) 2)
  end.

Definition tri (i : Z) : Z :=
  tri_fuel (Z.to_nat i) i.

Definition tri_sequence (n : Z) : list Z :=
  map tri (Zseq 0 (Z.to_nat (n + 1))).

Definition problem_130_pre (n : Z) : Prop :=
  0 <= n.

Definition problem_130_spec (n : Z) (out : list Z) : Prop :=
  0 <= n /\ out = tri_sequence n.

Definition tri_seq_int_range (n : Z) : Prop :=
  (forall i, 0 <= i <= n -> INT_MIN <= tri i <= INT_MAX) /\
  (forall i, 2 <= i <= n ->
     INT_MIN <= 1 + Z.quot i 2 <= INT_MAX /\
     INT_MIN <= tri (i - 1) + tri (i - 2) + 1 + Z.quot (i + 1) 2 <= INT_MAX).

Lemma tri_sequence_Zlength : forall n,
  0 <= n ->
  Zlength (tri_sequence n) = n + 1.
Proof.
  intros n Hn.
  unfold tri_sequence.
  rewrite Zlength_correct.
  rewrite length_map, Zseq_length.
  lia.
Qed.

Lemma tri_sequence_Znth : forall n i,
  0 <= i <= n ->
  Znth i (tri_sequence n) 0 = tri i.
Proof.
  intros n i Hi.
  unfold tri_sequence, Znth.
  rewrite (@nth_indep Z
            (map tri (Zseq 0 (Z.to_nat (n + 1)))) (Z.to_nat i)
            0 (tri 0)).
  2:{
    rewrite length_map, Zseq_length.
    lia.
  }
  rewrite map_nth with (d := 0%Z).
  rewrite Zseq_nth by lia.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma tri_sequence_sublist_snoc : forall n i,
  0 <= i <= n ->
  sublist 0 (i + 1) (tri_sequence n) =
  sublist 0 i (tri_sequence n) ++ tri i :: nil.
Proof.
  intros n i Hi.
  pose proof (tri_sequence_Zlength n ltac:(lia)) as Hlen.
  rewrite (sublist_split 0 (i + 1) i).
  - rewrite (sublist_single 0 i (tri_sequence n)).
    + rewrite tri_sequence_Znth by lia.
      reflexivity.
    + rewrite Hlen. lia.
  - lia.
  - rewrite Hlen. lia.
Qed.

Lemma tri_sequence_sublist_Znth : forall n i j,
  0 <= j < i ->
  i <= n + 1 ->
  Znth (j - 0) (sublist 0 i (tri_sequence n)) 0 = tri j.
Proof.
  intros n i j Hj Hi.
  replace (j - 0) with j by lia.
  rewrite Znth_sublist0 by lia.
  apply tri_sequence_Znth.
  lia.
Qed.

Lemma tri_fuel_stable_ge : forall fuel i,
  0 <= i ->
  (Z.to_nat i <= fuel)%nat ->
  tri_fuel fuel i = tri i.
Proof.
  intro fuel.
  pattern fuel.
  apply lt_wf_ind.
  clear fuel.
  intros fuel IH i Hi Hle.
  unfold tri.
  destruct fuel as [|fuel'].
  - assert (i = 0) by lia.
    subst; reflexivity.
  - destruct (Z.to_nat i) as [|ki] eqn:Hki.
    + assert (i = 0) by lia.
      subst; reflexivity.
    + simpl.
      destruct (Z.eqb i 0) eqn:Hi0.
      { reflexivity. }
      destruct (Z.eqb i 1) eqn:Hi1.
      { reflexivity. }
      destruct (Z.even i) eqn:Hiev.
      { reflexivity. }
      apply Z.eqb_neq in Hi0.
      apply Z.eqb_neq in Hi1.
      rewrite (IH fuel' ltac:(lia) (i - 2)).
      2: lia.
      2: {
        rewrite Z2Nat.inj_sub by lia.
        rewrite Hki.
        lia.
      }
      rewrite (IH ki ltac:(lia) (i - 2)).
      2: lia.
      2: {
        rewrite Z2Nat.inj_sub by lia.
        rewrite Hki.
        lia.
      }
      reflexivity.
Qed.

Lemma tri_even_quot_by_even : forall i,
  2 <= i ->
  Z.even i = true ->
  tri i = 1 + Z.quot i 2.
Proof.
  intros i Hi Heven.
  unfold tri.
  destruct (Z.to_nat i) as [|fuel] eqn:Hfuel; [lia|].
  cbn [tri_fuel].
  destruct (Z.eqb i 0) eqn:Hi0; [apply Z.eqb_eq in Hi0; lia|].
  destruct (Z.eqb i 1) eqn:Hi1; [apply Z.eqb_eq in Hi1; lia|].
  rewrite Heven.
  reflexivity.
Qed.

Lemma tri_even_quot : forall i,
  2 <= i ->
  Z.rem i 2 = 0 ->
  tri i = 1 + Z.quot i 2.
Proof.
  intros i Hi Hrem.
  apply tri_even_quot_by_even; [lia|].
  apply Z.even_spec.
  exists (Z.quot i 2).
  pose proof (Z.quot_rem' i 2).
  lia.
Qed.

Lemma tri_odd_quot : forall i,
  2 <= i ->
  Z.rem i 2 <> 0 ->
  tri i = tri (i - 1) + tri (i - 2) + 1 + Z.quot (i + 1) 2.
Proof.
  intros i Hi Hrem.
  assert (Hodd : Z.even i = false).
  {
    destruct (Z.even i) eqn:Heven; [|reflexivity].
    apply Z.even_spec in Heven.
    destruct Heven as [q Hq].
    exfalso.
    apply Hrem.
    rewrite Hq.
    replace (2 * q) with (q * 2) by lia.
    rewrite Z.rem_mul; lia.
  }
  assert (Hi_ge3 : 3 <= i).
  {
    assert (i <> 2) by (intro Hcontra; subst; apply Hrem; reflexivity).
    lia.
  }
  unfold tri at 1.
  destruct (Z.to_nat i) as [|fuel] eqn:Hfuel; [lia|].
  cbn [tri_fuel].
  destruct (Z.eqb i 0) eqn:Hi0; [apply Z.eqb_eq in Hi0; lia|].
  destruct (Z.eqb i 1) eqn:Hi1; [apply Z.eqb_eq in Hi1; lia|].
  rewrite Hodd.
  replace (tri_fuel fuel (i - 2)) with (tri (i - 2)).
  2:{
    symmetry.
    apply tri_fuel_stable_ge; [lia|].
    rewrite Z2Nat.inj_sub by lia.
    rewrite Hfuel.
    lia.
  }
  replace (1 + Z.quot (i - 1) 2) with (tri (i - 1)).
  2:{
    rewrite tri_even_quot_by_even; [reflexivity|lia|].
    replace (i - 1) with (i + -1) by lia.
    rewrite Z.even_add.
    rewrite Hodd.
    reflexivity.
  }
  ring.
Qed.

Lemma tri_fuel_nonneg : forall fuel i,
  0 <= i ->
  0 <= tri_fuel fuel i.
Proof.
  induction fuel; intros i Hi; cbn [tri_fuel].
  - destruct (Z.eqb i 1); lia.
  - destruct (Z.eqb i 0) eqn:Hi0; [lia|].
    destruct (Z.eqb i 1) eqn:Hi1; [lia|].
    apply Z.eqb_neq in Hi0.
    apply Z.eqb_neq in Hi1.
    destruct (Z.even i); [pose proof (Z.quot_pos i 2 ltac:(lia) ltac:(lia)); lia|].
    pose proof (IHfuel (i - 2) ltac:(lia)).
    pose proof (Z.quot_pos (i - 1) 2 ltac:(lia) ltac:(lia)).
    pose proof (Z.quot_pos (i + 1) 2 ltac:(lia) ltac:(lia)).
    lia.
Qed.

Lemma tri_nonneg : forall i,
  0 <= i ->
  0 <= tri i.
Proof.
  intros i Hi.
  unfold tri.
  apply tri_fuel_nonneg.
  exact Hi.
Qed.

Lemma tri_even_expr_range : forall n i,
  tri_seq_int_range n ->
  2 <= i <= n ->
  INT_MIN <= 1 + Z.quot i 2 <= INT_MAX.
Proof.
  intros n i Hrange Hi.
  destruct Hrange as [_ Hstep].
  pose proof (Hstep i Hi) as [H _].
  exact H.
Qed.

Lemma tri_odd_expr_range : forall n i,
  tri_seq_int_range n ->
  2 <= i <= n ->
  INT_MIN <= tri (i - 1) + tri (i - 2) + 1 + Z.quot (i + 1) 2 <= INT_MAX.
Proof.
  intros n i Hrange Hi.
  destruct Hrange as [_ Hstep].
  pose proof (Hstep i Hi) as [_ H].
  exact H.
Qed.

Lemma tri_odd_expr_partial_range_1 : forall n i,
  tri_seq_int_range n ->
  2 <= i <= n ->
  INT_MIN <= tri (i - 1) + tri (i - 2) <= INT_MAX.
Proof.
  intros n i Hrange Hi.
  pose proof (tri_odd_expr_range n i Hrange Hi) as Hfull.
  pose proof (tri_nonneg (i - 1) ltac:(lia)).
  pose proof (tri_nonneg (i - 2) ltac:(lia)).
  assert (0 <= Z.quot (i + 1) 2) by (apply Z.quot_pos; lia).
  lia.
Qed.

Lemma tri_odd_expr_partial_range_2 : forall n i,
  tri_seq_int_range n ->
  2 <= i <= n ->
  INT_MIN <= tri (i - 1) + tri (i - 2) + 1 <= INT_MAX.
Proof.
  intros n i Hrange Hi.
  pose proof (tri_odd_expr_range n i Hrange Hi) as Hfull.
  pose proof (tri_nonneg (i - 1) ltac:(lia)).
  pose proof (tri_nonneg (i - 2) ltac:(lia)).
  assert (0 <= Z.quot (i + 1) 2) by (apply Z.quot_pos; lia).
  lia.
Qed.

Lemma tri_sequence_even_snoc : forall n i,
  2 <= i <= n ->
  Z.rem i 2 = 0 ->
  sublist 0 (i + 1) (tri_sequence n) =
  sublist 0 i (tri_sequence n) ++ (1 + Z.quot i 2) :: nil.
Proof.
  intros n i Hi Hrem.
  rewrite tri_sequence_sublist_snoc by lia.
  rewrite tri_even_quot by lia.
  reflexivity.
Qed.

Lemma tri_sequence_odd_snoc : forall n i,
  2 <= i <= n ->
  Z.rem i 2 <> 0 ->
  sublist 0 (i + 1) (tri_sequence n) =
  sublist 0 i (tri_sequence n) ++
  (Znth (i - 1 - 0) (sublist 0 i (tri_sequence n)) 0 +
   Znth (i - 2 - 0) (sublist 0 i (tri_sequence n)) 0 +
   1 + Z.quot (i + 1) 2) :: nil.
Proof.
  intros n i Hi Hrem.
  rewrite tri_sequence_sublist_snoc by lia.
  rewrite tri_odd_quot by lia.
  rewrite !tri_sequence_sublist_Znth by lia.
  reflexivity.
Qed.

Lemma tri_sequence_sublist_2 : forall n,
  1 <= n ->
  sublist 0 2 (tri_sequence n) = 1 :: 3 :: nil.
Proof.
  intros n Hn.
  rewrite tri_sequence_sublist_snoc with (i := 1) by lia.
  rewrite tri_sequence_sublist_snoc with (i := 0) by lia.
  unfold sublist.
  simpl.
  reflexivity.
Qed.

Lemma tri_sequence_spec : forall n,
  0 <= n ->
  problem_130_spec n (tri_sequence n).
Proof.
  intros n Hn.
  unfold problem_130_spec.
  split; auto.
Qed.

Lemma tri_seq_int_range_value : forall n i,
  tri_seq_int_range n ->
  0 <= i <= n ->
  INT_MIN <= tri i <= INT_MAX.
Proof.
  intros n i [Hrange _] Hi.
  apply Hrange; lia.
Qed.

Lemma tri_seq_int_range_step : forall n i,
  tri_seq_int_range n ->
  2 <= i <= n ->
  INT_MIN <= 1 + Z.quot i 2 <= INT_MAX /\
  INT_MIN <= tri (i - 1) + tri (i - 2) + 1 + Z.quot (i + 1) 2 <= INT_MAX.
Proof.
  intros n i [_ Hstep] Hi.
  apply Hstep; lia.
Qed.

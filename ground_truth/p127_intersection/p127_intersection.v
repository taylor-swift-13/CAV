(* spec/127 *)
(*You are given two intervals,
where each interval is a pair of integers. For example, interval = (start, end) = (1, 2).
The given intervals are closed which means that the interval (start, end)
includes both start and end.
For each given interval, it is assumed that its start is less or equal its end.
Your task is to determine whether the length of intersection of these two
intervals is a prime number.
Example, the intersection of the intervals (1, 3), (2, 4) is (2, 3)
which its length is 1, which not a prime number.
If the length of the intersection is a prime number, return "YES",
otherwise, return "NO".
If the two intervals don't intersect, return "NO".

[input/output] samples:
intersection((1, 2), (2, 3)) ==> "NO"
intersection((-1, 1), (0, 4)) ==> "NO"
intersection((-3, -1), (-5, 5)) ==> "YES" *)

(* 引入所需的基础 Coq 库 *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

(* 区间为闭区间，且满足 start <= end *)


Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Import naive_C_Rules.

Local Open Scope Z_scope.

Definition interval_pair (l : list Z) : Z * Z :=
  (Znth 0 l 0, Znth 1 l 0).

Definition inter_start (i1 i2 : list Z) : Z :=
  Z.max (Znth 0 i1 0) (Znth 0 i2 0).

Definition inter_end (i1 i2 : list Z) : Z :=
  Z.min (Znth 1 i1 0) (Znth 1 i2 0).

Definition inter_len (i1 i2 : list Z) : Z :=
  inter_end i1 i2 - inter_start i1 i2.

Definition prime_prefix (i n : Z) : Prop :=
  forall d, 2 <= d < i -> Z.rem n d <> 0.

Definition prime_len (n : Z) : Prop :=
  2 <= n /\ forall d, 2 <= d /\ d * d <= n -> Z.rem n d <> 0.

Definition problem_127_pre (i1 i2 : list Z) : Prop :=
  let '(s1,e1) := ((interval_pair i1)) in
  let '(s2,e2) := ((interval_pair i2)) in (s1 <= e1)%Z /\ (s2 <= e2)%Z.

Definition problem_127_spec (i1 i2 : list Z) (output : Z) : Prop :=
  (output = 1 /\ inter_start i1 i2 <= inter_end i1 i2 /\ prime_len (inter_len i1 i2)) \/
  (output = 0 /\ (inter_end i1 i2 < inter_start i1 i2 \/ ~ prime_len (inter_len i1 i2))).

Definition interval_int_range (l : list Z) : Prop :=
  Zlength l = 2 /\
  forall i, 0 <= i < 2 -> -1000000000 <= Znth i l 0 <= 1000000000.

Lemma prime_prefix_2 : forall n,
  prime_prefix 2 n.
Proof.
  unfold prime_prefix.
  intros n d H.
  lia.
Qed.

Lemma prime_prefix_step : forall i n,
  prime_prefix i n ->
  Z.rem n i <> 0 ->
  prime_prefix (i + 1) n.
Proof.
  unfold prime_prefix.
  intros i n Hpre Hmod d Hd.
  destruct (Z.eq_dec d i) as [-> | Hne].
  - exact Hmod.
  - apply Hpre. lia.
Qed.

Lemma prime_len_false_small : forall n,
  n < 2 ->
  ~ prime_len n.
Proof.
  unfold prime_len.
  intros n Hlt H.
  lia.
Qed.

Lemma prime_len_false_divisor : forall i n,
  2 <= i ->
  i * i <= n ->
  Z.rem n i = 0 ->
  ~ prime_len n.
Proof.
  unfold prime_len.
  intros i n Hi Hsquare Hmod [_ Hprime].
  specialize (Hprime i ltac:(lia)).
  contradiction.
Qed.

Lemma prime_len_true_from_prefix : forall i n,
  2 <= n ->
  2 <= i ->
  i * i > n ->
  prime_prefix i n ->
  prime_len n.
Proof.
  unfold prime_prefix, prime_len.
  intros i n Hn Hi Hexit Hpre.
  split.
  - assumption.
  - intros d [Hd Hsquare].
    apply Hpre.
    assert (d < i) by nia.
    lia.
Qed.

Lemma problem_127_spec_true : forall i1 i2,
  prime_len (inter_len i1 i2) ->
  problem_127_spec i1 i2 1.
Proof.
  intros i1 i2 Hprime_len.
  unfold problem_127_spec.
  left.
  split; [reflexivity |].
  split.
  - unfold inter_len in Hprime_len.
    destruct Hprime_len as [Hlen _].
    lia.
  - exact Hprime_len.
Qed.

Lemma problem_127_spec_false : forall i1 i2,
  ~ prime_len (inter_len i1 i2) ->
  problem_127_spec i1 i2 0.
Proof.
  intros i1 i2 Hnot.
  unfold problem_127_spec.
  right.
  split; [reflexivity |].
  right.
  exact Hnot.
Qed.

Lemma inter_len_range_safe : forall i1 i2,
  interval_int_range i1 ->
  interval_int_range i2 ->
  -2000000000 <= inter_len i1 i2 <= 2000000000.
Proof.
  intros i1 i2 [_ Hr1] [_ Hr2].
  unfold inter_len, inter_start, inter_end.
  pose proof (Hr1 0 ltac:(lia)).
  pose proof (Hr1 1 ltac:(lia)).
  pose proof (Hr2 0 ltac:(lia)).
  pose proof (Hr2 1 ltac:(lia)).
  nia.
Qed.

Lemma prime_loop_next_bound_127 : forall i n,
  2 <= i ->
  i <= 46340 ->
  n <= 2000000000 ->
  i * i <= n ->
  i + 1 <= 46340.
Proof.
  intros.
  nia.
Qed.

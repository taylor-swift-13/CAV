(* spec/80 *)
(* def is_happy(s):
"""You are given a string s.
Your task is to check if the string is happy or not.
A string is happy if its length is at least 3 and every 3 consecutive letters are distinct
For example:
is_happy(a) => False
is_happy(aa) => False
is_happy(abcd) => True
is_happy(aabb) => False
is_happy(adb) => True
is_happy(xyy) => False
""" *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.

(*
  problem_80_spec s output

  描述了 is_happy 函数的行为，其中输入是一个 ascii 字符列表。
  当且仅当 `output` 是输入列表 `s` 的正确快乐性判断时，该命题为真。

  一个列表是快乐的，当且仅当：
  1. 其长度至少为 3。
  2. 所有连续的 3 个字符都是不同的。
*)

Require Import Coq.ZArith.ZArith.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition problem_80_pre (s : list Z) : Prop :=
  True.

Definition problem_80_spec (s : list Z) (output : Z) : Prop :=
  match bool_of output with
  | true =>
      3 <= Zlength s /\
      forall i, 0 <= i -> i + 2 < Zlength s ->
        Znth i s 0 <> Znth (i + 1) s 0 /\
        Znth i s 0 <> Znth (i + 2) s 0 /\
        Znth (i + 1) s 0 <> Znth (i + 2) s 0
  | false =>
      Zlength s < 3 \/
      exists i, 0 <= i /\ i + 2 < Zlength s /\
        (Znth i s 0 = Znth (i + 1) s 0 \/
         Znth i s 0 = Znth (i + 2) s 0 \/
         Znth (i + 1) s 0 = Znth (i + 2) s 0)
  end.

Definition ascii_range (s : list Z) : Prop :=
  string_bridge.ascii_range s.

Definition happy_window_end (k : Z) (s : list Z) : Prop :=
  Znth k s 0 <> Znth (k - 1) s 0 /\
  Znth k s 0 <> Znth (k - 2) s 0 /\
  Znth (k - 1) s 0 <> Znth (k - 2) s 0.

Definition happy_prefix (i : Z) (s : list Z) : Prop :=
  forall k, 2 <= k < i -> happy_window_end k s.

Definition happy_adjacent (i : Z) (s : list Z) : Prop :=
  Znth (i - 1) s 0 <> Znth (i - 2) s 0.

Lemma happy_prefix_2 : forall s,
  happy_prefix 2 s.
Proof.
  unfold happy_prefix.
  intros s k Hk.
  lia.
Qed.

Lemma happy_adjacent_2 : forall s,
  Znth 1 s 0 <> Znth 0 s 0 ->
  happy_adjacent 2 s.
Proof.
  unfold happy_adjacent.
  intros s H.
  replace (2 - 1) with 1 by lia.
  replace (2 - 2) with 0 by lia.
  exact H.
Qed.

Lemma happy_adjacent_step : forall i s,
  Znth i s 0 <> Znth (i - 1) s 0 ->
  happy_adjacent (i + 1) s.
Proof.
  unfold happy_adjacent.
  intros i s H.
  replace (i + 1 - 1) with i by lia.
  replace (i + 1 - 2) with (i - 1) by lia.
  exact H.
Qed.

Lemma happy_prefix_step : forall i s,
  happy_prefix i s ->
  happy_adjacent i s ->
  Znth i s 0 <> Znth (i - 1) s 0 ->
  Znth i s 0 <> Znth (i - 2) s 0 ->
  happy_prefix (i + 1) s.
Proof.
  unfold happy_prefix, happy_window_end.
  intros i s Hprefix Hadj Hprev1 Hprev2 k Hk.
  destruct (Z_lt_ge_dec k i).
  - apply Hprefix. lia.
  - assert (k = i) by lia.
    subst k.
    unfold happy_adjacent in Hadj.
    repeat split; assumption.
Qed.

Lemma problem_80_spec_short : forall s,
  Zlength s < 3 ->
  problem_80_spec s 0.
Proof.
  intros s Hshort.
  unfold problem_80_spec, bool_of.
  change (Z.eqb 0 1) with false.
  left.
  exact Hshort.
Qed.

Lemma problem_80_spec_false_first_pair : forall s,
  3 <= Zlength s ->
  Znth 0 s 0 = Znth 1 s 0 ->
  problem_80_spec s 0.
Proof.
  intros s Hlen Heq.
  unfold problem_80_spec, bool_of.
  change (Z.eqb 0 1) with false.
  right.
  exists 0.
  repeat split; try lia.
  left.
  exact Heq.
Qed.

Lemma problem_80_spec_false_prev1 : forall s i,
  2 <= i ->
  i < Zlength s ->
  Znth i s 0 = Znth (i - 1) s 0 ->
  problem_80_spec s 0.
Proof.
  intros s i Hi Hbound Heq.
  unfold problem_80_spec, bool_of.
  change (Z.eqb 0 1) with false.
  right.
  exists (i - 2).
  repeat split; try lia.
  right.
  right.
  replace (i - 2 + 1) with (i - 1) by lia.
  replace (i - 2 + 2) with i by lia.
  symmetry.
  exact Heq.
Qed.

Lemma problem_80_spec_false_prev2 : forall s i,
  2 <= i ->
  i < Zlength s ->
  Znth i s 0 = Znth (i - 2) s 0 ->
  problem_80_spec s 0.
Proof.
  intros s i Hi Hbound Heq.
  unfold problem_80_spec, bool_of.
  change (Z.eqb 0 1) with false.
  right.
  exists (i - 2).
  repeat split; try lia.
  right.
  left.
  replace (i - 2 + 2) with i by lia.
  symmetry.
  exact Heq.
Qed.

Lemma problem_80_spec_true : forall s i,
  ascii_range s ->
  i >= Zlength s ->
  3 <= Zlength s ->
  happy_prefix i s ->
  problem_80_spec s 1.
Proof.
  intros s i _ Hexit Hlen Hprefix.
  unfold problem_80_spec, bool_of.
  change (Z.eqb 1 1) with true.
  split; [lia |].
  intros j Hj Hbound.
  assert (Hwin : happy_window_end (j + 2) s) by (apply Hprefix; lia).
  unfold happy_window_end in Hwin.
  destruct Hwin as [Hneq32 [Hneq31 Hneq21]].
  repeat split.
  - intro Heq.
    apply Hneq21.
    replace (j + 2 - 1) with (j + 1) by lia.
    replace (j + 2 - 2) with j by lia.
    symmetry.
    exact Heq.
  - intro Heq.
    apply Hneq31.
    replace (j + 2 - 2) with j by lia.
    symmetry.
    exact Heq.
  - intro Heq.
    apply Hneq32.
    replace (j + 2 - 1) with (j + 1) by lia.
    symmetry.
    exact Heq.
Qed.

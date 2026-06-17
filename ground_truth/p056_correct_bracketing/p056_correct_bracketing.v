(* spec/56 *)
(* def correct_bracketing(brackets: str):
 brackets is a string of "<" and ">".
return True if every opening bracket has a corresponding closing bracket.

>>> correct_bracketing("<")
False
>>> correct_bracketing("<>")
True
>>> correct_bracketing("<<><>>")
True
>>> correct_bracketing("><<>")
False
*)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.
Import ListNotations.

Local Open Scope Z_scope.

Definition problem_56_pre (brackets : list Z) : Prop :=
  Forall (fun c => c = 60 \/ c = 62) brackets.

Definition bool_of (z : Z) : bool :=
  Z.eqb z 1.

Definition angle_delta (x : Z) : Z :=
  if Z.eqb x 60 then 1 else if Z.eqb x 62 then -1 else 0.

Fixpoint angle_level_upto_nat (n : nat) (l : list Z) : Z :=
  match n with
  | O => 0
  | S n' => angle_level_upto_nat n' l + angle_delta (Znth (Z.of_nat n') l 0)
  end.

Definition angle_level_upto (i : Z) (l : list Z) : Z :=
  angle_level_upto_nat (Z.to_nat i) l.

Definition angle_nonnegative_prefix (i : Z) (l : list Z) : Prop :=
  forall k, 0 <= k < i -> 0 <= angle_level_upto (k + 1) l.

Definition angle_balanced (l : list Z) : Prop :=
  angle_level_upto (Zlength l) l = 0 /\
  angle_nonnegative_prefix (Zlength l) l.

Definition problem_56_spec (brackets : list Z) (output : Z) : Prop :=
  bool_of output = true <-> angle_balanced brackets.

Lemma Znth_In_range_56 : forall (l : list Z) k d,
  0 <= k < Zlength l ->
  In (Znth k l d) l.
Proof.
  intros l k d Hk.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hk.
  lia.
Qed.

Lemma angle_level_upto_0 : forall l,
  angle_level_upto 0 l = 0.
Proof.
  intros l.
  unfold angle_level_upto.
  reflexivity.
Qed.

Lemma angle_nonnegative_prefix_0 : forall l,
  angle_nonnegative_prefix 0 l.
Proof.
  unfold angle_nonnegative_prefix.
  intros l k Hk.
  lia.
Qed.

Lemma angle_level_upto_step_open : forall i l,
  0 <= i ->
  Znth i l 0 = 60 ->
  angle_level_upto (i + 1) l = angle_level_upto i l + 1.
Proof.
  intros i l Hi Hx.
  unfold angle_level_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  unfold angle_delta.
  rewrite Hx.
  rewrite Z.eqb_refl.
  reflexivity.
Qed.

Lemma angle_level_upto_step_close : forall i l,
  0 <= i ->
  Znth i l 0 = 62 ->
  angle_level_upto (i + 1) l = angle_level_upto i l - 1.
Proof.
  intros i l Hi Hx.
  unfold angle_level_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  unfold angle_delta.
  rewrite Hx.
  replace (Z.eqb 62 60) with false by reflexivity.
  replace (Z.eqb 62 62) with true by reflexivity.
  lia.
Qed.

Lemma angle_nonnegative_prefix_step : forall i l level,
  angle_nonnegative_prefix i l ->
  angle_level_upto (i + 1) l = level ->
  0 <= level ->
  angle_nonnegative_prefix (i + 1) l.
Proof.
  unfold angle_nonnegative_prefix.
  intros i l level Hprefix Hlevel Hnonneg k Hk.
  destruct (Z_lt_ge_dec k i).
  - apply Hprefix. lia.
  - assert (k = i) by lia.
    subst k.
    rewrite Hlevel.
    lia.
Qed.

Lemma problem_56_pre_char : forall l k,
  problem_56_pre l ->
  0 <= k < Zlength l ->
  Znth k l 0 = 60 \/ Znth k l 0 = 62.
Proof.
  intros l k Hpre Hk.
  unfold problem_56_pre in Hpre.
  rewrite Forall_forall in Hpre.
  apply Hpre.
  apply Znth_In_range_56.
  exact Hk.
Qed.

Lemma problem_56_pre_nonzero : forall l n,
  Zlength l = n ->
  problem_56_pre l ->
  forall k, 0 <= k < n -> Znth k l 0 <> 0.
Proof.
  intros l n Hlen Hpre k Hk.
  destruct (problem_56_pre_char l k Hpre ltac:(lia)); lia.
Qed.

Lemma problem_56_spec_true : forall l,
  angle_level_upto (Zlength l) l = 0 ->
  angle_nonnegative_prefix (Zlength l) l ->
  problem_56_spec l 1.
Proof.
  intros l Hlevel Hprefix.
  unfold problem_56_spec, bool_of, angle_balanced.
  simpl.
  split.
  - intros _. split; assumption.
  - intros _. reflexivity.
Qed.

Lemma problem_56_spec_false_negative : forall l i,
  0 <= i ->
  i < Zlength l ->
  angle_level_upto (i + 1) l < 0 ->
  problem_56_spec l 0.
Proof.
  intros l i Hi Hbound Hneg.
  unfold problem_56_spec, bool_of, angle_balanced.
  simpl.
  split.
  - discriminate.
  - intros [_ Hprefix].
    specialize (Hprefix i ltac:(lia)).
    lia.
Qed.

Lemma problem_56_spec_false_final : forall l level,
  angle_level_upto (Zlength l) l = level ->
  level <> 0 ->
  problem_56_spec l 0.
Proof.
  intros l level Hlevel Hneq.
  unfold problem_56_spec, bool_of, angle_balanced.
  simpl.
  split.
  - discriminate.
  - intros [Hbalanced _].
    rewrite Hlevel in Hbalanced.
    lia.
Qed.

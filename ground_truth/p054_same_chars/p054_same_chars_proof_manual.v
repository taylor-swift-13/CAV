Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p054_same_chars Require Import p054_same_chars_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import List Ascii String.
Require Import Coq.Strings.Ascii.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Import naive_C_Rules.
Require Import p054_same_chars.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p054_same_chars.v so public contract files expose definitions only. *)

Lemma Znth_In_range : forall (l : list Z) k d,
  0 <= k < Zlength l ->
  In (Znth k l d) l.
Proof.
  intros l k d Hk.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hk.
  lia.
Qed.
Lemma nat_of_ascii_ascii_of : forall z,
  0 <= z < 256 ->
  nat_of_ascii (ascii_of z) = Z.to_nat z.
Proof.
  intros z Hz.
  unfold ascii_of.
  apply nat_ascii_embedding.
  lia.
Qed.
Lemma list_ascii_of_string_string_of_list : forall l,
  list_ascii_of_string (string_of_list l) = map ascii_of l.
Proof.
  induction l as [| c rest IH]; simpl; auto.
  rewrite IH.
  reflexivity.
Qed.
Lemma ascii_of_inj_range_54 : forall a b,
  0 <= a < 256 ->
  0 <= b < 256 ->
  ascii_of a = ascii_of b ->
  a = b.
Proof.
  intros a b Ha Hb Heq.
  apply (f_equal nat_of_ascii) in Heq.
  unfold ascii_of in Heq.
  repeat rewrite nat_ascii_embedding in Heq by lia.
  lia.
Qed.
Lemma same_chars_set_to_ascii_set : forall s0 s1,
  same_chars_set s0 s1 ->
  forall c : ascii,
    In c (list_ascii_of_string (string_of_list s0)) <->
    In c (list_ascii_of_string (string_of_list s1)).
Proof.
  intros s0 s1 [Hall01 Hall10] c.
  repeat rewrite list_ascii_of_string_string_of_list.
  split; intros Hin.
  - apply in_map_iff in Hin.
    destruct Hin as [z [Hzc HzIn]].
    apply in_map_iff.
    exists z.
    split; [assumption |].
    destruct (In_nth s0 z 0 HzIn) as [n [Hn Hnth]].
    subst z.
    unfold same_chars_all, same_chars_prefix, char_in in Hall01.
    specialize (Hall01 (Z.of_nat n)).
    unfold Znth in Hall01.
    rewrite Nat2Z.id in Hall01.
    apply Hall01.
    rewrite Zlength_correct; lia.
  - apply in_map_iff in Hin.
    destruct Hin as [z [Hzc HzIn]].
    apply in_map_iff.
    exists z.
    split; [assumption |].
    destruct (In_nth s1 z 0 HzIn) as [n [Hn Hnth]].
    subst z.
    unfold same_chars_all, same_chars_prefix, char_in in Hall10.
    specialize (Hall10 (Z.of_nat n)).
    unfold Znth in Hall10.
    rewrite Nat2Z.id in Hall10.
    apply Hall10.
    rewrite Zlength_correct; lia.
Qed.
Lemma ascii_set_missing_left_false : forall s0 s1 i,
  ascii_range s0 ->
  ascii_range s1 ->
  0 <= i < Zlength s0 ->
  ~ char_in (Znth i s0 0) s1 ->
  ~ (forall c : ascii,
      In c (list_ascii_of_string (string_of_list s0)) <->
      In c (list_ascii_of_string (string_of_list s1))).
Proof.
  intros s0 s1 i Hr0 Hr1 Hi Hnot Hall.
  specialize (Hall (ascii_of (Znth i s0 0))) as [Hin01 _].
  repeat rewrite list_ascii_of_string_string_of_list in Hin01.
  assert (Hin0 : In (ascii_of (Znth i s0 0)) (map ascii_of s0)).
  {
    apply in_map.
    apply Znth_In_range. lia.
  }
  specialize (Hin01 Hin0).
  apply in_map_iff in Hin01.
  destruct Hin01 as [z [Hz Hzin]].
  apply Hnot.
  assert (Hzrange : 0 <= z < 256).
  {
    destruct (In_nth s1 z 0 Hzin) as [k [Hk Hznth]].
    rewrite <- Hznth.
    unfold ascii_range in Hr1.
    specialize (Hr1 (Z.of_nat k)).
    unfold Znth in Hr1.
    rewrite Nat2Z.id in Hr1.
    apply Hr1.
    rewrite Zlength_correct; lia.
  }
  replace (Znth i s0 0) with z.
  - exact Hzin.
  - pose proof (ascii_of_inj_range_54 z (Znth i s0 0)
      Hzrange (Hr0 i Hi) Hz) as Heq.
    exact Heq.
Qed.
Lemma ascii_set_missing_right_false : forall s0 s1 i,
  ascii_range s0 ->
  ascii_range s1 ->
  0 <= i < Zlength s1 ->
  ~ char_in (Znth i s1 0) s0 ->
  ~ (forall c : ascii,
      In c (list_ascii_of_string (string_of_list s0)) <->
      In c (list_ascii_of_string (string_of_list s1))).
Proof.
  intros s0 s1 i Hr0 Hr1 Hi Hnot Hall.
  specialize (Hall (ascii_of (Znth i s1 0))) as [_ Hin10].
  repeat rewrite list_ascii_of_string_string_of_list in Hin10.
  assert (Hin1 : In (ascii_of (Znth i s1 0)) (map ascii_of s1)).
  {
    apply in_map.
    apply Znth_In_range. lia.
  }
  specialize (Hin10 Hin1).
  apply in_map_iff in Hin10.
  destruct Hin10 as [z [Hz Hzin]].
  apply Hnot.
  assert (Hzrange : 0 <= z < 256).
  {
    destruct (In_nth s0 z 0 Hzin) as [k [Hk Hznth]].
    rewrite <- Hznth.
    unfold ascii_range in Hr0.
    specialize (Hr0 (Z.of_nat k)).
    unfold Znth in Hr0.
    rewrite Nat2Z.id in Hr0.
    apply Hr0.
    rewrite Zlength_correct; lia.
  }
  replace (Znth i s1 0) with z.
  - exact Hzin.
  - pose proof (ascii_of_inj_range_54 z (Znth i s1 0)
      Hzrange (Hr1 i Hi) Hz) as Heq.
    exact Heq.
Qed.
Lemma same_chars_prefix_zero : forall s0 s1,
  same_chars_prefix 0 s0 s1.
Proof.
  unfold same_chars_prefix.
  intros; lia.
Qed.
Lemma same_chars_prefix_step : forall i s0 s1,
  0 <= i ->
  same_chars_prefix i s0 s1 ->
  char_in (Znth i s0 0) s1 ->
  same_chars_prefix (i + 1) s0 s1.
Proof.
  unfold same_chars_prefix.
  intros i s0 s1 Hi Hprefix Hin k Hk.
  destruct (Z.eq_dec k i) as [-> | Hne].
  - exact Hin.
  - apply Hprefix; lia.
Qed.
Lemma same_chars_all_intro : forall s0 s1,
  same_chars_prefix (Zlength s0) s0 s1 ->
  same_chars_all s0 s1.
Proof.
  intros; exact H.
Qed.
Lemma problem_54_spec_true : forall s0 s1,
  same_chars_all s0 s1 ->
  same_chars_all s1 s0 ->
  problem_54_spec s0 s1 1.
Proof.
  intros s0 s1 Hall01 Hall10.
  unfold problem_54_spec, bool_of.
  simpl.
  split.
  - intros _. apply same_chars_set_to_ascii_set.
    split; assumption.
  - intros _. reflexivity.
Qed.
Lemma problem_54_spec_false_left : forall i s0 s1,
  ascii_range s0 ->
  ascii_range s1 ->
  0 <= i < Zlength s0 ->
  ~ char_in (Znth i s0 0) s1 ->
  problem_54_spec s0 s1 0.
Proof.
  unfold same_chars_set, same_chars_all, same_chars_prefix.
  intros i s0 s1 Hr0 Hr1 Hi Hnot.
  unfold problem_54_spec, bool_of.
  simpl.
  split; intros H.
  - discriminate.
  - exfalso.
    eapply ascii_set_missing_left_false.
    + exact Hr0.
    + exact Hr1.
    + exact Hi.
    + exact Hnot.
    + exact H.
Qed.
Lemma problem_54_spec_false_right : forall i s0 s1,
  ascii_range s0 ->
  ascii_range s1 ->
  0 <= i < Zlength s1 ->
  ~ char_in (Znth i s1 0) s0 ->
  problem_54_spec s0 s1 0.
Proof.
  unfold same_chars_set, same_chars_all, same_chars_prefix.
  intros i s0 s1 Hr0 Hr1 Hi Hnot.
  unfold problem_54_spec, bool_of.
  simpl.
  split; intros H.
  - discriminate.
  - exfalso.
    eapply ascii_set_missing_right_false.
    + exact Hr0.
    + exact Hr1.
    + exact Hi.
    + exact Hnot.
    + exact H.
Qed.


Ltac same_chars_pre :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia.

Ltac solve_no_zero_goal :=
  match goal with
  | Hnz : no_zero ?l |- forall k : Z, 0 <= k /\ k < ?n -> Znth k ?l 0 <> 0 =>
      intros k Hk;
      destruct Hnz as [_ Hforall];
      apply Hforall;
      lia
  | Hnz : no_zero ?l, Hlen : Zlength ?l = ?n
    |- Znth 0 ?l 0 <> 0 /\ Znth (?n - 1) ?l 0 <> 0 =>
      destruct Hnz as [Hpos Hforall];
      split; apply Hforall; lia
  | Hnz : no_zero ?l |- Znth 0 ?l 0 <> 0 =>
      destruct Hnz as [Hpos Hforall];
      apply Hforall;
      lia
  | Hnz : no_zero ?l, Hlen : Zlength ?l = ?n
    |- Znth (?n - 1) ?l 0 <> 0 =>
      destruct Hnz as [Hpos Hforall];
      apply Hforall;
      lia
  end.

Lemma proof_of_p054_same_chars_partial_solve_wit_1_pure : p054_same_chars_partial_solve_wit_1_pure.
Proof.
  pre_process.
  entailer!; try solve_no_zero_goal; try lia.
Qed.

Lemma proof_of_p054_same_chars_partial_solve_wit_2_pure : p054_same_chars_partial_solve_wit_2_pure.
Proof.
  pre_process.
  entailer!; try solve_no_zero_goal; try lia.
Qed.

Lemma proof_of_p054_same_chars_partial_solve_wit_4_pure : p054_same_chars_partial_solve_wit_4_pure.
Proof.
  pre_process.
  entailer!; try solve_no_zero_goal; try lia.
Qed.

Lemma proof_of_p054_same_chars_partial_solve_wit_6_pure : p054_same_chars_partial_solve_wit_6_pure.
Proof.
  pre_process.
  entailer!; try solve_no_zero_goal; try lia.
Qed.

Lemma proof_of_p054_same_chars_entail_wit_1 : p054_same_chars_entail_wit_1.
Proof.
  unfold p054_same_chars_entail_wit_1.
  intros.
  same_chars_pre.
  entailer!.
  apply same_chars_prefix_zero.
Qed. 

Lemma proof_of_p054_same_chars_entail_wit_2 : p054_same_chars_entail_wit_2.
Proof.
  unfold p054_same_chars_entail_wit_2.
  intros.
  same_chars_pre.
  entailer!.
  apply same_chars_prefix_step; try lia.
  assumption.
  assumption.
Qed. 

Lemma proof_of_p054_same_chars_entail_wit_3 : p054_same_chars_entail_wit_3.
Proof.
  unfold p054_same_chars_entail_wit_3.
  intros.
  same_chars_pre.
  assert (i = Zlength l0) by lia.
  subst i.
  entailer!.
  apply same_chars_prefix_zero.
Qed. 

Lemma proof_of_p054_same_chars_entail_wit_4 : p054_same_chars_entail_wit_4.
Proof.
  unfold p054_same_chars_entail_wit_4.
  intros.
  same_chars_pre.
  entailer!.
  apply same_chars_prefix_step; try lia.
  assumption.
  assumption.
Qed. 

Lemma proof_of_p054_same_chars_return_wit_1 : p054_same_chars_return_wit_1.
Proof.
  unfold p054_same_chars_return_wit_1.
  intros.
  same_chars_pre.
  assert (i = Zlength l1) by lia.
  subst i.
  entailer!; try solve_no_zero_goal.
  apply problem_54_spec_true; unfold same_chars_all; assumption.
Qed. 

Lemma proof_of_p054_same_chars_return_wit_2 : p054_same_chars_return_wit_2.
Proof.
  unfold p054_same_chars_return_wit_2.
  intros.
  same_chars_pre.
  entailer!; try solve_no_zero_goal.
  apply problem_54_spec_false_right with (i := i); try lia; try assumption.
Qed. 

Lemma proof_of_p054_same_chars_return_wit_3 : p054_same_chars_return_wit_3.
Proof.
  unfold p054_same_chars_return_wit_3.
  intros.
  same_chars_pre.
  entailer!; try solve_no_zero_goal.
  apply problem_54_spec_false_left with (i := i); try lia; try assumption.
Qed. 

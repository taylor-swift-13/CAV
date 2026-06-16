Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260607_044032_p054_same_chars Require Import p054_same_chars_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import string_bridge.
Require Import p054_same_chars.
Local Open Scope sac.

(* ===== Helper lemmas ===== *)

Lemma list_ascii_of_string_of_list : forall (l : list Z),
  list_ascii_of_string (string_of_list l) = map ascii_of l.
Proof.
  induction l as [| hd tl IH].
  - reflexivity.
  - simpl. f_equal. exact IH.
Qed.

Lemma In_Znth_Z : forall (l : list Z) (z : Z),
  In z l -> exists k, 0 <= k < Zlength l /\ Znth k l 0 = z.
Proof.
  intros l z Hin.
  apply In_nth with (d := 0) in Hin as [n [Hn Hnth]].
  exists (Z.of_nat n).
  split.
  - rewrite Zlength_correct. lia.
  - unfold Znth.
    destruct (Z_lt_dec (Z.of_nat n) 0) as [Hlt | Hge]; [lia | ].
    rewrite Nat2Z.id. exact Hnth.
Qed.

Lemma Znth_In_Z : forall (l : list Z) (i : Z),
  0 <= i < Zlength l -> In (Znth i l 0) l.
Proof.
  intros l i Hi.
  unfold Znth.
  destruct (Z_lt_dec i 0) as [Hlt | Hge]; [lia | ].
  apply nth_In.
  rewrite Zlength_correct in Hi. lia.
Qed.

Lemma ascii_of_inj : forall x y,
  0 <= x < 256 -> 0 <= y < 256 -> ascii_of x = ascii_of y -> x = y.
Proof.
  intros x y Hx Hy Heq.
  unfold ascii_of in Heq.
  apply f_equal with (f := nat_of_ascii) in Heq.
  assert (H256 : Z.to_nat 256 = 256%nat) by reflexivity.
  assert (Hnx : (Z.to_nat x < 256)%nat).
  { assert (Hlt : (Z.to_nat x < Z.to_nat 256)%nat).
    { apply (proj1 (Z2Nat.inj_lt x 256 ltac:(lia) ltac:(lia))). lia. }
    lia. }
  assert (Hny : (Z.to_nat y < 256)%nat).
  { assert (Hlt : (Z.to_nat y < Z.to_nat 256)%nat).
    { apply (proj1 (Z2Nat.inj_lt y 256 ltac:(lia) ltac:(lia))). lia. }
    lia. }
  rewrite nat_ascii_embedding in Heq by exact Hnx.
  rewrite nat_ascii_embedding in Heq by exact Hny.
  apply Z2Nat.inj; [lia | lia | exact Heq].
Qed.

Lemma ascii_range_in : forall (l : list Z) (z : Z),
  ascii_range l -> In z l -> 0 <= z < 256.
Proof.
  intros l z Har Hin.
  apply In_Znth_Z in Hin as [k [Hk Hval]].
  rewrite <- Hval.
  exact (Har k Hk).
Qed.

Lemma extend_same_chars_prefix_step : forall (i n : Z) (l0 l1 : list Z),
  Zlength l0 = n ->
  0 <= i ->
  i < n ->
  same_chars_prefix i l0 l1 ->
  char_in (Znth i (app l0 (cons 0 nil)) 0) l1 ->
  same_chars_prefix (i + 1) l0 l1.
Proof.
  intros i n l0 l1 Hlen Hi Hin Hsp Hcin.
  unfold same_chars_prefix, char_in in *.
  rewrite app_Znth1 in Hcin by lia.
  intros k Hk.
  destruct (Z.eq_dec k i) as [-> | Hne].
  - exact Hcin.
  - apply Hsp. lia.
Qed.

Lemma same_chars_prefix_to_all : forall (i n0 : Z) (l0 l1 : list Z),
  Zlength l0 = n0 ->
  i >= n0 ->
  i <= n0 ->
  same_chars_prefix i l0 l1 ->
  same_chars_all l0 l1.
Proof.
  intros i n0 l0 l1 Hlen Hge Hle Hsp.
  unfold same_chars_all.
  assert (Hi : i = n0) by lia.
  rewrite Hlen. rewrite <- Hi. exact Hsp.
Qed.

(* ===== Main proofs ===== *)

Lemma proof_of_p054_same_chars_entail_wit_1 : p054_same_chars_entail_wit_1.
Proof.
  pre_process. subst.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    unfold same_chars_prefix. intros k Hk. lia.
Qed.

Lemma proof_of_p054_same_chars_entail_wit_2 : p054_same_chars_entail_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    apply extend_same_chars_prefix_step with (n := n0); try lia; assumption.
Qed.

Lemma proof_of_p054_same_chars_entail_wit_3 : p054_same_chars_entail_wit_3.
Proof.
  pre_process.
  split_pure_spatial.
  - replace i with n0 by lia. cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    apply same_chars_prefix_to_all with (i := i) (n0 := n0); try lia; assumption.
Qed.

Lemma proof_of_p054_same_chars_entail_wit_4 : p054_same_chars_entail_wit_4.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    unfold same_chars_prefix. intros k Hk. lia.
Qed.

Lemma proof_of_p054_same_chars_entail_wit_5 : p054_same_chars_entail_wit_5.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    apply extend_same_chars_prefix_step with (n := n1); try lia; assumption.
Qed.

Lemma proof_of_p054_same_chars_return_wit_1 : p054_same_chars_return_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    assert (Hsal01 : same_chars_all l0 l1) by assumption.
    assert (Hsal10 : same_chars_all l1 l0).
    { apply same_chars_prefix_to_all with (i := i) (n0 := n1); try lia; assumption. }
    unfold problem_54_spec, bool_of.
    rewrite !list_ascii_of_string_of_list.
    split.
    + intros _.
      intro c. split.
      * intro Hcl0.
        apply in_map_iff in Hcl0 as [z [Hz Hinz]].
        apply In_Znth_Z in Hinz as [k [Hk Hval]].
        unfold same_chars_all, same_chars_prefix, char_in in Hsal01.
        pose proof (Hsal01 k Hk) as Hzl1.
        rewrite Hval in Hzl1.
        rewrite <- Hz. apply in_map. exact Hzl1.
      * intro Hcl1.
        apply in_map_iff in Hcl1 as [z [Hz Hinz]].
        apply In_Znth_Z in Hinz as [k [Hk Hval]].
        unfold same_chars_all, same_chars_prefix, char_in in Hsal10.
        pose proof (Hsal10 k Hk) as Hzl0.
        rewrite Hval in Hzl0.
        rewrite <- Hz. apply in_map. exact Hzl0.
    + intros _. reflexivity.
Qed.

Lemma proof_of_p054_same_chars_return_wit_2 : p054_same_chars_return_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    unfold problem_54_spec, bool_of.
    rewrite !list_ascii_of_string_of_list.
    split.
    + intro Hf. discriminate.
    + intro Hiff. exfalso.
      assert (Hvi_in_l1 : In (Znth i l1 0) l1).
      { apply Znth_In_Z. lia. }
      assert (Hvi_range : 0 <= Znth i l1 0 < 256).
      { assert (Har : ascii_range l1) by assumption. apply Har. lia. }
      assert (Hnot_in_l0 : ~In (Znth i l1 0) l0).
      { assert (Hnc : ~char_in (Znth i (app l1 (cons 0 nil)) 0) l0) by assumption.
        unfold char_in in Hnc.
        rewrite app_Znth1 in Hnc by lia.
        exact Hnc. }
      assert (Hc_l1 : In (ascii_of (Znth i l1 0)) (map ascii_of l1)).
      { apply in_map. exact Hvi_in_l1. }
      pose proof (Hiff (ascii_of (Znth i l1 0))) as [_ Hrl0].
      apply Hrl0 in Hc_l1.
      apply in_map_iff in Hc_l1 as [z' [Hza Hz'l0]].
      assert (Hz'_range : 0 <= z' < 256).
      { apply ascii_range_in with (l := l0); [assumption | exact Hz'l0]. }
      assert (Hz'_eq : z' = Znth i l1 0).
      { apply ascii_of_inj; [exact Hz'_range | exact Hvi_range | exact Hza]. }
      rewrite Hz'_eq in Hz'l0.
      exact (Hnot_in_l0 Hz'l0).
Qed.

Lemma proof_of_p054_same_chars_return_wit_3 : p054_same_chars_return_wit_3.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    unfold problem_54_spec, bool_of.
    rewrite !list_ascii_of_string_of_list.
    split.
    + intro Hf. discriminate.
    + intro Hiff. exfalso.
      assert (Hvi_in_l0 : In (Znth i l0 0) l0).
      { apply Znth_In_Z. lia. }
      assert (Hvi_range : 0 <= Znth i l0 0 < 256).
      { assert (Har : ascii_range l0) by assumption. apply Har. lia. }
      assert (Hnot_in_l1 : ~In (Znth i l0 0) l1).
      { assert (Hnc : ~char_in (Znth i (app l0 (cons 0 nil)) 0) l1) by assumption.
        unfold char_in in Hnc.
        rewrite app_Znth1 in Hnc by lia.
        exact Hnc. }
      assert (Hc_l0 : In (ascii_of (Znth i l0 0)) (map ascii_of l0)).
      { apply in_map. exact Hvi_in_l0. }
      pose proof (Hiff (ascii_of (Znth i l0 0))) as [Hrl1 _].
      apply Hrl1 in Hc_l0.
      apply in_map_iff in Hc_l0 as [z' [Hza Hz'l1]].
      assert (Hz'_range : 0 <= z' < 256).
      { apply ascii_range_in with (l := l1); [assumption | exact Hz'l1]. }
      assert (Hz'_eq : z' = Znth i l0 0).
      { apply ascii_of_inj; [exact Hz'_range | exact Hvi_range | exact Hza]. }
      rewrite Hz'_eq in Hz'l1.
      exact (Hnot_in_l1 Hz'l1).
Qed.


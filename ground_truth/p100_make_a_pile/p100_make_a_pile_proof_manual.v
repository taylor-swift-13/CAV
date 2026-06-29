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
From SimpleC.EE.CAV.ground_truth_p100_make_a_pile Require Import p100_make_a_pile_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p100_make_a_pile.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p100_make_a_pile.v so public contract files expose definitions only. *)

Lemma make_pile_Zlength : forall n,
  0 <= n ->
  Zlength (make_pile n) = n.
Proof.
  intros n Hn.
  unfold make_pile.
  rewrite Zlength_correct.
  rewrite length_map, Zseq_length.
  lia.
Qed.
Lemma make_pile_Znth : forall n i,
  0 <= i < n ->
  Znth i (make_pile n) 0 = n + 2 * i.
Proof.
  intros n i Hi.
  unfold make_pile.
  unfold Znth.
  eapply nth_error_nth.
  rewrite nth_error_map.
  rewrite nth_error_nth' with (d := 0%Z).
  - rewrite Zseq_nth by lia.
    rewrite Z2Nat.id by lia.
    reflexivity.
  - rewrite Zseq_length.
    lia.
Qed.
Lemma make_pile_sublist_snoc : forall n i,
  0 <= i < n ->
  sublist 0 (i + 1) (make_pile n) =
  sublist 0 i (make_pile n) ++ (n + 2 * i) :: nil.
Proof.
  intros n i Hi.
  pose proof (make_pile_Zlength n ltac:(lia)) as Hlen.
  assert (Hsplit_lo : 0 <= 0 <= i) by lia.
  assert (Hsplit_hi : i <= i + 1 <= Zlength (make_pile n))
    by (rewrite Hlen; lia).
  rewrite (@sublist_split Z 0 (i + 1) i (make_pile n) Hsplit_lo Hsplit_hi).
  rewrite (sublist_single 0 i (make_pile n)).
  - rewrite make_pile_Znth by lia.
    reflexivity.
  - rewrite Hlen.
    lia.
Qed.
Lemma problem_100_spec_make_pile : forall n,
  n > 0 ->
  problem_100_spec n (make_pile n).
Proof.
  intros n Hn.
  unfold problem_100_spec.
  split; [lia |].
  split.
  - apply make_pile_Zlength. lia.
  - intros i Hi.
    apply make_pile_Znth. lia.
Qed.


Lemma proof_of_p100_make_a_pile_safety_wit_3 : p100_make_a_pile_safety_wit_3.
Proof.
  pre_process.
  match goal with
  | H: pile_int_range n0 |- _ => pose proof (H i ltac:(lia))
  end.
  entailer!.
Qed. 

Lemma proof_of_p100_make_a_pile_safety_wit_4 : p100_make_a_pile_safety_wit_4.
Proof.
  pre_process.
  match goal with
  | H: pile_int_range n0 |- _ => pose proof (H i ltac:(lia))
  end.
  entailer!.
Qed. 

Lemma proof_of_p100_make_a_pile_entail_wit_1 : p100_make_a_pile_entail_wit_1.
Proof.
  pre_process.
  subst.
  sep_apply IntArray.undef_full_to_undef_seg.
  entailer!.
  rewrite IntArray.seg_empty.
  entailer!.
  apply make_pile_Zlength.
  lia.
Qed. 

Lemma proof_of_p100_make_a_pile_entail_wit_2 : p100_make_a_pile_entail_wit_2.
Proof.
  pre_process.
  rewrite make_pile_sublist_snoc by lia.
  entailer!.
Qed. 

Lemma proof_of_p100_make_a_pile_return_wit_1 : p100_make_a_pile_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = n0) by lia.
  subst i.
  Exists (make_pile n0) n0 data_2.
  rewrite sublist_self by lia.
  sep_apply (IntArray.seg_to_full data_2 0 n0).
  replace (data_2 + 0 * sizeof (INT)) with data_2 by lia.
  replace (n0 - 0) with n0 by lia.
  rewrite (IntArray.undef_seg_empty data_2 n0).
  entailer!.
  apply problem_100_spec_make_pile.
  lia.
Qed. 

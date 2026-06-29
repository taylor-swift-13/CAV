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
From SimpleC.EE.CAV.ground_truth_p106_f Require Import p106_f_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Nat.
Require Import List.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p106_f.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p106_f.v so public contract files expose definitions only. *)

Lemma triangular_0 :
  triangular 0 = 0.
Proof. reflexivity. Qed.
Lemma factorial_0 :
  factorial 0 = 1.
Proof. reflexivity. Qed.
Lemma triangular_step : forall i,
  0 <= i ->
  triangular (i + 1) = triangular i + (i + 1).
Proof.
  intros i Hi.
  unfold triangular.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.leb (i + 1) 0) with false by (symmetry; apply Z.leb_gt; lia).
  replace (i + 1 - 1) with i by lia.
  reflexivity.
Qed.
Lemma factorial_step : forall i,
  0 <= i ->
  factorial (i + 1) = factorial i * (i + 1).
Proof.
  intros i Hi.
  destruct (Z.eq_dec i 0) as [-> | Hnz].
  - reflexivity.
  - unfold factorial.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    simpl.
    replace (Z.leb (i + 1) 1) with false by (symmetry; apply Z.leb_gt; lia).
    replace (i + 1 - 1) with i by lia.
    ring.
Qed.
Lemma f_seq_Zlength : forall n,
  0 <= n ->
  Zlength (f_seq n) = n.
Proof.
  intros n Hn.
  unfold f_seq.
  rewrite Zlength_correct.
  rewrite length_map, Zseq_length.
  lia.
Qed.
Lemma f_seq_Znth : forall n i,
  0 <= i < n ->
  Znth i (f_seq n) 0 = f_elem (i + 1).
Proof.
  intros n i Hi.
  unfold f_seq.
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
Lemma f_seq_sublist_snoc : forall n i,
  0 <= i < n ->
  sublist 0 (i + 1) (f_seq n) =
  sublist 0 i (f_seq n) ++ f_elem (i + 1) :: nil.
Proof.
  intros n i Hi.
  pose proof (f_seq_Zlength n ltac:(lia)) as Hlen.
  assert (Hsplit_lo : 0 <= 0 <= i) by lia.
  assert (Hsplit_hi : i <= i + 1 <= Zlength (f_seq n))
    by (rewrite Hlen; lia).
  rewrite (@sublist_split Z 0 (i + 1) i (f_seq n) Hsplit_lo Hsplit_hi).
  rewrite (sublist_single 0 i (f_seq n)).
  - rewrite f_seq_Znth by lia.
    reflexivity.
  - rewrite Hlen.
    lia.
Qed.
Lemma f_elem_even_rem : forall i,
  Z.rem i 2 = 0 ->
  f_elem i = factorial i.
Proof.
  intros i Hrem.
  unfold f_elem.
  rewrite Zeven_rem.
  rewrite Hrem.
  reflexivity.
Qed.
Lemma f_elem_odd_rem : forall i,
  Z.rem i 2 <> 0 ->
  f_elem i = triangular i.
Proof.
  intros i Hrem.
  unfold f_elem.
  rewrite Zeven_rem.
  apply Z.eqb_neq in Hrem.
  rewrite Hrem.
  reflexivity.
Qed.
Lemma problem_106_spec_f_seq : forall n,
  0 <= n ->
  problem_106_spec n (f_seq n).
Proof.
  intros n Hn.
  unfold problem_106_spec.
  split; [lia | reflexivity].
Qed.


Lemma proof_of_p106_f_safety_wit_4 : p106_f_safety_wit_4.
Proof.
  pre_process.
  subst s.
  match goal with
  | H: f_seq_int_range n0 |- _ => pose proof (H (i + 1) ltac:(lia)) as Hrange
  end.
  rewrite <- triangular_step by lia.
  entailer!.
Qed. 

Lemma proof_of_p106_f_safety_wit_7 : p106_f_safety_wit_7.
Proof.
  pre_process.
  subst p.
  match goal with
  | H: f_seq_int_range n0 |- _ => pose proof (H (i + 1) ltac:(lia)) as Hrange
  end.
  rewrite <- factorial_step by lia.
  entailer!.
Qed. 

Lemma proof_of_p106_f_entail_wit_1 : p106_f_entail_wit_1.
Proof.
  pre_process.
  subst.
  rewrite f_seq_Zlength by lia.
  rewrite triangular_0.
  rewrite factorial_0.
  sep_apply IntArray.undef_full_to_undef_seg.
  entailer!.
  rewrite IntArray.seg_empty.
  entailer!.
Qed. 

Lemma proof_of_p106_f_entail_wit_2_1 : p106_f_entail_wit_2_1.
Proof.
  pre_process.
  assert (Hsnext : s + (i + 1) = triangular (i + 1)).
  { subst s. symmetry. apply triangular_step. lia. }
  assert (Hpnext : p * (i + 1) = factorial (i + 1)).
  { subst p. symmetry. apply factorial_step. lia. }
  rewrite f_seq_sublist_snoc by lia.
  replace (p * (i + 1)) with (f_elem (i + 1)).
  2:{
    rewrite Hpnext.
    apply f_elem_even_rem.
    assumption.
  }
  andp_cancel; auto; try lia.
  apply f_elem_even_rem.
  assumption.
Qed. 

Lemma proof_of_p106_f_entail_wit_2_2 : p106_f_entail_wit_2_2.
Proof.
  pre_process.
  assert (Hsnext : s + (i + 1) = triangular (i + 1)).
  { subst s. symmetry. apply triangular_step. lia. }
  assert (Hpnext : p * (i + 1) = factorial (i + 1)).
  { subst p. symmetry. apply factorial_step. lia. }
  rewrite f_seq_sublist_snoc by lia.
  replace (s + (i + 1)) with (f_elem (i + 1)).
  2:{
    rewrite Hsnext.
    apply f_elem_odd_rem.
    assumption.
  }
  andp_cancel; auto; try lia.
  apply f_elem_odd_rem.
  assumption.
Qed. 

Lemma proof_of_p106_f_return_wit_1 : p106_f_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = n0) by lia.
  subst i.
  Exists (f_seq n0) n0 data_2.
  rewrite sublist_self by lia.
  sep_apply (IntArray.seg_to_full data_2 0 n0).
  replace (data_2 + 0 * sizeof (INT)) with data_2 by lia.
  replace (n0 - 0) with n0 by lia.
  rewrite (IntArray.undef_seg_empty data_2 n0).
  entailer!.
  apply problem_106_spec_f_seq.
  lia.
Qed. 

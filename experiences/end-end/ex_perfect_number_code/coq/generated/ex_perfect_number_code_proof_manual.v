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
From SimpleC.EE.CAV.verify_20260605_200638v_ex_perfect_number_code Require Import ex_perfect_number_code_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import ex_perfect_number_code.
Require Import ex_perfect_number_code_helper.
Local Open Scope sac.

Lemma aliquot_sum_from_fuel_nonneg :
  forall fuel n d,
    1 <= d ->
    0 <= aliquot_sum_from_fuel_tail n d fuel.
Proof.
  induction fuel as [| fuel IH]; intros n d Hd; simpl.
  - lia.
  - destruct (Z.geb d n) eqn:Hdgeb.
    + lia.
    + destruct (Z.eqb (n % ( d ) ) 0) eqn:Heq.
      * specialize (IH n (d + 1)).
        assert (1 <= d + 1) by lia.
        lia.
      * specialize (IH n (d + 1)).
        assert (1 <= d + 1) by lia.
        lia.
Qed.

Lemma aliquot_sum_from_fuel_tail_eq :
  forall fuel n d,
    aliquot_sum_from_fuel_tail n d fuel = aliquot_sum_from_fuel n d fuel.
Proof.
  induction fuel as [| fuel IH]; intros n d; simpl.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Lemma aliquot_sum_tail_z_nonneg :
  forall n d,
    1 <= d ->
    0 <= aliquot_sum_tail_z n d.
Proof.
  intros n d Hd.
  unfold aliquot_sum_tail_z.
  apply aliquot_sum_from_fuel_nonneg.
  exact Hd.
Qed.

Lemma aliquot_sum_tail_z_start :
  forall n,
    0 < n ->
    aliquot_sum_tail_z n 1 = aliquot_sum_z n.
Proof.
  intros n Hn.
  unfold aliquot_sum_tail_z, aliquot_sum_z.
  replace (n - 1 + 1) with n by lia.
  rewrite aliquot_sum_from_fuel_tail_eq.
  reflexivity.
Qed.

Lemma aliquot_sum_tail_z_stop :
  forall n,
    0 < n ->
    aliquot_sum_tail_z n n = 0.
Proof.
  intros n Hn.
  unfold aliquot_sum_tail_z.
  replace (n - n + 1) with 1 by lia.
  simpl.
  destruct (Z.geb n n) eqn:Hdgeb.
  - reflexivity.
  - assert (Z.geb n n = true) as Hrefl by (apply Z.geb_le; lia).
    rewrite Hrefl in Hdgeb.
    discriminate.
Qed.

Lemma aliquot_sum_tail_z_step_divides :
  forall n d,
    1 <= d ->
    d < n ->
    n % ( d ) = 0 ->
    aliquot_sum_tail_z n d = d + aliquot_sum_tail_z n (d + 1).
Proof.
  intros n d Hd Hlt Hmod.
  unfold aliquot_sum_tail_z at 1 2.
  replace (Z.to_nat (n - d + 1)) with (S (Z.to_nat (n - d))) by lia.
  replace (n - (d + 1) + 1) with (n - d) by lia.
  simpl.
  destruct (Z.geb d n) eqn:Hdgeb.
  - apply Z.geb_le in Hdgeb.
    lia.
  - rewrite Hmod.
    simpl.
    reflexivity.
Qed.

Lemma aliquot_sum_tail_z_step_not_divides :
  forall n d,
    1 <= d ->
    d < n ->
    n % ( d ) <> 0 ->
    aliquot_sum_tail_z n d = aliquot_sum_tail_z n (d + 1).
Proof.
  intros n d Hd Hlt Hmod.
  unfold aliquot_sum_tail_z at 1 2.
  replace (Z.to_nat (n - d + 1)) with (S (Z.to_nat (n - d))) by lia.
  replace (n - (d + 1) + 1) with (n - d) by lia.
  simpl.
  destruct (Z.geb d n) eqn:Hdgeb.
  - apply Z.geb_le in Hdgeb.
    lia.
  - destruct (Z.eqb (n % ( d ) ) 0) eqn:Heq.
    + apply Z.eqb_eq in Heq.
      contradiction.
    + reflexivity.
Qed.

Lemma proof_of_ex_perfect_number_code_safety_wit_5 : ex_perfect_number_code_safety_wit_5.
Proof.
  pre_process.
  assert (Hstep : aliquot_sum_tail_z n_pre d = d + aliquot_sum_tail_z n_pre (d + 1)).
  { apply aliquot_sum_tail_z_step_divides; lia. }
  assert (Hnonneg_next : 0 <= aliquot_sum_tail_z n_pre (d + 1)).
  { apply aliquot_sum_tail_z_nonneg; lia. }
  rewrite Hstep in H6.
  entailer!.
Qed.

Lemma proof_of_ex_perfect_number_code_entail_wit_1 : ex_perfect_number_code_entail_wit_1.
Proof.
  pre_process.
  assert (Hstart : aliquot_sum_tail_z n_pre 1 = aliquot_sum_z n_pre).
  { apply aliquot_sum_tail_z_start; lia. }
  assert (Hnonneg : 0 <= aliquot_sum_tail_z n_pre 1).
  { apply aliquot_sum_tail_z_nonneg; lia. }
  rewrite Hstart in Hnonneg.
  rewrite Hstart.
  entailer!.
Qed.

Lemma proof_of_ex_perfect_number_code_entail_wit_2_1 : ex_perfect_number_code_entail_wit_2_1.
Proof.
  pre_process.
  assert (Hstep : aliquot_sum_tail_z n_pre d = d + aliquot_sum_tail_z n_pre (d + 1)).
  { apply aliquot_sum_tail_z_step_divides; lia. }
  assert (Hnonneg_next : 0 <= aliquot_sum_tail_z n_pre (d + 1)).
  { apply aliquot_sum_tail_z_nonneg; lia. }
  rewrite Hstep in H6.
  entailer!.
Qed.

Lemma proof_of_ex_perfect_number_code_entail_wit_2_2 : ex_perfect_number_code_entail_wit_2_2.
Proof.
  pre_process.
  assert (Hstep : aliquot_sum_tail_z n_pre d = aliquot_sum_tail_z n_pre (d + 1)).
  { apply aliquot_sum_tail_z_step_not_divides; lia. }
  assert (Hnonneg_next : 0 <= aliquot_sum_tail_z n_pre (d + 1)).
  { apply aliquot_sum_tail_z_nonneg; lia. }
  rewrite Hstep in H6.
  entailer!.
Qed.

Lemma proof_of_ex_perfect_number_code_entail_wit_3 : ex_perfect_number_code_entail_wit_3.
Proof.
  pre_process.
  assert (d = n_pre) by lia.
  subst d.
  assert (Hstop : aliquot_sum_tail_z n_pre n_pre = 0).
  { apply aliquot_sum_tail_z_stop; lia. }
  rewrite Hstop in H5.
  entailer!.
Qed.

Lemma proof_of_ex_perfect_number_code_return_wit_1 : ex_perfect_number_code_return_wit_1.
Proof.
  pre_process.
  unfold ex_perfect_number_code_spec.
  subst sum.
  destruct (Z.eqb (aliquot_sum_z n_pre) n_pre) eqn:Heq.
  - apply Z.eqb_eq in Heq.
    lia.
  - destruct (Z.gtb (aliquot_sum_z n_pre) n_pre) eqn:Hgt.
    + apply Z.gtb_lt in Hgt.
      lia.
    + entailer!.
Qed.

Lemma proof_of_ex_perfect_number_code_return_wit_2 : ex_perfect_number_code_return_wit_2.
Proof.
  pre_process.
  unfold ex_perfect_number_code_spec.
  subst sum.
  destruct (Z.eqb (aliquot_sum_z n_pre) n_pre) eqn:Heq.
  - apply Z.eqb_eq in Heq.
    lia.
  - destruct (Z.gtb (aliquot_sum_z n_pre) n_pre) eqn:Hgt.
    + entailer!.
    + assert ((aliquot_sum_z n_pre >? n_pre) = true) as Hgt_true.
      { apply Z.gtb_lt. lia. }
      rewrite Hgt_true in Hgt.
      discriminate.
Qed.

Lemma proof_of_ex_perfect_number_code_return_wit_3 : ex_perfect_number_code_return_wit_3.
Proof.
  pre_process.
  unfold ex_perfect_number_code_spec.
  subst sum.
  destruct (Z.eqb (aliquot_sum_z n_pre) n_pre) eqn:Heq.
  - entailer!.
  - apply Z.eqb_neq in Heq.
    lia.
Qed.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260605_055926v_count_set_bits Require Import count_set_bits_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import count_set_bits.
Local Open Scope sac.

Lemma count_set_bits_fuel_zero :
  forall fuel, count_set_bits_fuel 0 fuel = 0.
Proof.
  destruct fuel; reflexivity.
Qed.

Lemma count_set_bits_div2_nonneg :
  forall n, 0 <= n -> 0 <= Z.div n 2.
Proof.
  intros n Hn.
  apply Z.div_pos; lia.
Qed.

Lemma count_set_bits_div2_le_pred :
  forall fuel n,
    0 < n ->
    n <= Z.of_nat (S fuel) ->
    Z.div n 2 <= Z.of_nat fuel.
Proof.
  intros fuel n Hpos Hbound.
  destruct (Z_lt_ge_dec n 2) as [Hlt | Hge].
  - assert (n = 1) by lia.
    subst n.
    rewrite Z.div_small; lia.
  - assert (1 <= Z.of_nat fuel) by lia.
    apply Z.div_le_upper_bound; lia.
Qed.

Lemma count_set_bits_fuel_irrelevant :
  forall n,
    0 <= n ->
    forall fuel1 fuel2,
      n <= Z.of_nat fuel1 ->
      n <= Z.of_nat fuel2 ->
      count_set_bits_fuel n fuel1 = count_set_bits_fuel n fuel2.
Proof.
  refine (well_founded_induction
            (well_founded_ltof _ Z.to_nat)
            (fun n =>
               0 <= n ->
               forall fuel1 fuel2,
                 n <= Z.of_nat fuel1 ->
                 n <= Z.of_nat fuel2 ->
                 count_set_bits_fuel n fuel1 = count_set_bits_fuel n fuel2)
            _).
  intros n IH Hn fuel1 fuel2 Hbound1 Hbound2.
  destruct (Z_le_gt_dec n 0) as [Hle | Hgt].
  - assert (n = 0) by (apply Z.le_antisymm; [exact Hle | exact Hn]).
    subst n.
    repeat rewrite count_set_bits_fuel_zero.
    reflexivity.
  - destruct fuel1 as [| fuel1]; [lia|].
    destruct fuel2 as [| fuel2]; [lia|].
    simpl.
    assert (Hleb : Z.leb n 0 = false) by (apply Z.leb_gt; lia).
    rewrite Hleb.
    f_equal.
    apply IH.
    + apply Z2Nat.inj_lt; [apply count_set_bits_div2_nonneg; lia | lia | apply Z.div_lt; lia].
    + apply count_set_bits_div2_nonneg; lia.
    + apply count_set_bits_div2_le_pred; lia.
    + apply count_set_bits_div2_le_pred; lia.
Qed.

Lemma count_set_bits_fuel_enough :
  forall fuel n,
    0 <= n ->
    n <= Z.of_nat fuel ->
    count_set_bits_fuel n fuel = count_set_bits_z n.
Proof.
  intros fuel n Hn Hbound.
  unfold count_set_bits_z.
  eapply count_set_bits_fuel_irrelevant.
  - exact Hn.
  - exact Hbound.
  - rewrite Z2Nat.id by lia.
    lia.
Qed.

Lemma count_set_bits_fuel_le_input :
  forall fuel n,
    0 <= n ->
    n <= Z.of_nat fuel ->
    count_set_bits_fuel n fuel <= n.
Proof.
  induction fuel as [| fuel IH]; intros n Hn Hbound.
  - assert (n = 0) by lia.
    subst n.
    simpl.
    lia.
  - simpl.
    destruct (Z.leb_spec n 0) as [Hle | Hgt].
    + lia.
    + assert (Hdiv_nonneg : 0 <= Z.div n 2) by
          (apply count_set_bits_div2_nonneg; lia).
      assert (Hdiv_bound : Z.div n 2 <= Z.of_nat fuel) by
          (apply count_set_bits_div2_le_pred; lia).
      specialize (IH (Z.div n 2) Hdiv_nonneg Hdiv_bound).
      assert (Hrem_bound : 0 <= Z.rem n 2 < 2) by
          (apply Z.rem_bound_pos; lia).
      assert (Hrem_eq : Z.rem n 2 = n mod 2) by
          (apply Z.rem_mod_nonneg; lia).
      pose proof (Z.div_mod n 2 ltac:(lia)) as Hdecomp.
      rewrite Hrem_eq.
      lia.
Qed.

Lemma count_set_bits_fuel_nonneg :
  forall fuel n, 0 <= count_set_bits_fuel n fuel.
Proof.
  induction fuel as [| fuel IH]; intros n.
  - simpl. lia.
  - simpl.
    destruct (Z.leb_spec n 0) as [Hle | Hgt].
    + lia.
    + specialize (IH (Z.div n 2)).
      assert (0 <= Z.rem n 2 < 2) by (apply Z.rem_bound_pos; lia).
      lia.
Qed.

Lemma count_set_bits_z_nonneg :
  forall n, 0 <= count_set_bits_z n.
Proof.
  intros n.
  unfold count_set_bits_z.
  apply count_set_bits_fuel_nonneg.
Qed.

Lemma count_set_bits_z_le_input :
  forall n, 0 <= n -> count_set_bits_z n <= n.
Proof.
  intros n Hn.
  unfold count_set_bits_z.
  apply count_set_bits_fuel_le_input; lia.
Qed.

Lemma count_set_bits_z_step :
  forall n,
    0 < n ->
    count_set_bits_z n = Z.rem n 2 + count_set_bits_z (n ÷ 2).
Proof.
  intros n Hpos.
  unfold count_set_bits_z at 1.
  destruct (Z.to_nat n) as [| fuel] eqn:Hfuel.
  - destruct n; simpl in *; lia.
  - simpl.
    assert (Hleb : Z.leb n 0 = false) by (apply Z.leb_gt; lia).
    rewrite Hleb.
    rewrite count_set_bits_fuel_enough.
    + rewrite Z.quot_div_nonneg by lia.
      reflexivity.
    + apply count_set_bits_div2_nonneg; lia.
    + apply count_set_bits_div2_le_pred.
      * lia.
      * rewrite <- Hfuel.
        rewrite Z2Nat.id by lia.
        lia.
Qed.

Lemma proof_of_count_set_bits_safety_wit_6 : count_set_bits_safety_wit_6.
Proof.
  pre_process.
  assert (Hstep : count_set_bits_z n = Z.rem n 2 + count_set_bits_z (n ÷ 2)).
  { apply count_set_bits_z_step; lia. }
  assert (Hrem1 : Z.rem n 2 = 1).
  { exact H. }
  assert (Htotal_le : count_set_bits_z n_pre <= n_pre).
  { apply count_set_bits_z_le_input; lia. }
  assert (Htail_nonneg : 0 <= count_set_bits_z (n ÷ 2)).
  { apply count_set_bits_z_nonneg. }
  entailer!.
Qed.

Lemma proof_of_count_set_bits_entail_wit_1 : count_set_bits_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_count_set_bits_entail_wit_2_1 : count_set_bits_entail_wit_2_1.
Proof.
  pre_process.
  assert (Hstep : count_set_bits_z n = Z.rem n 2 + count_set_bits_z (n ÷ 2)).
  { apply count_set_bits_z_step; lia. }
  assert (Hrem1 : Z.rem n 2 = 1).
  { exact H. }
  entailer!.
  - eapply Z.le_trans with (m := n).
    + apply Z.quot_le_upper_bound; lia.
    + exact H2.
  - apply Z.quot_pos; lia.
Qed.

Lemma proof_of_count_set_bits_entail_wit_2_2 : count_set_bits_entail_wit_2_2.
Proof.
  pre_process.
  assert (Hstep : count_set_bits_z n = Z.rem n 2 + count_set_bits_z (n ÷ 2)).
  { apply count_set_bits_z_step; lia. }
  assert (Hmod0 : n % 2 = 0).
  { assert (0 <= n % 2 < 2) by (apply Z.rem_bound_pos; lia). lia. }
  assert (Hrem0 : Z.rem n 2 = 0).
  { exact Hmod0. }
  entailer!.
  - eapply Z.le_trans with (m := n).
    + apply Z.quot_le_upper_bound; lia.
    + exact H2.
  - apply Z.quot_pos; lia.
Qed.

Lemma proof_of_count_set_bits_return_wit_1 : count_set_bits_return_wit_1.
Proof.
  pre_process.
  assert (Hzero : count_set_bits_z n = 0).
  { unfold count_set_bits_z.
    destruct n; simpl in *; try reflexivity; lia.
  }
  entailer!.
Qed.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p131_digits Require Import p131_digits_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Lists.List Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import naive_C_Rules.
Require Import p131_digits.
Local Open Scope sac.
Require Import Coq.ZArith.Zwf.
Require Import Coq.Init.Wf.

Local Open Scope list_scope.

(* Proof helpers moved from p131_digits.v so public contract files expose definitions only. *)

Lemma Z_to_nat_nz_pos (n : Z) :
  0 <= n -> Z.to_nat n <> 0%nat -> n > 0.
Proof.
  intros Hn H. destruct (Z.eq_dec n 0) as [E | E].
  - subst. simpl in H. contradiction H. reflexivity.
  - lia.
Qed.
Lemma Z_to_nat_quot (n : Z) :
  0 <= n -> Z.to_nat (Z.quot n 10) = ((Z.to_nat n) / 10)%nat.
Proof.
  intros. rewrite Z.quot_div_nonneg by lia. rewrite Z2Nat.inj_div by lia. reflexivity.
Qed.
Lemma S_div_10_le (n : nat) : ((S n / 10)%nat <= n)%nat.
Proof.
  destruct n.
  - simpl; lia.
  - apply Nat.div_le_upper_bound; lia.
Qed.
Lemma Z_to_nat_S_pred (n : Z) :
  0 <= n -> Z.to_nat n <> 0%nat -> Z.to_nat n = S (Nat.pred (Z.to_nat n)).
Proof.
  intros. destruct (Z.to_nat n) eqn:E.
  - contradiction H0; reflexivity.
  - reflexivity.
Qed.
Lemma tail_odd_prod_fuel_step :
  forall fuel n prod has,
    n > 0 ->
    tail_odd_prod_fuel (S fuel) n prod has =
      if Z.odd (Z.rem n 10)
      then tail_odd_prod_fuel fuel (Z.quot n 10) (prod * (Z.rem n 10)) 1
      else tail_odd_prod_fuel fuel (Z.quot n 10) prod has.
Proof.
  intros. simpl tail_odd_prod_fuel. replace (Z.leb n 0) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.
Lemma tail_odd_prod_fuel_sufficient :
  forall fuel n prod has,
    0 <= n ->
    (Z.to_nat n <= fuel)%nat ->
    tail_odd_prod_fuel fuel n prod has = tail_odd_prod_fuel (Z.to_nat n) n prod has.
Proof.
  enough (forall n fuel prod has, 0 <= n -> (Z.to_nat n <= fuel)%nat -> tail_odd_prod_fuel fuel n prod has = tail_odd_prod_fuel (Z.to_nat n) n prod has).
  { intros; eauto. }
  intros n.
  induction n as [n IHn] using (well_founded_induction_type (Zwf_well_founded 0)).
  intros fuel prod has Hn Hfuel.
  destruct (Z.leb_spec n 0).
  - assert (n = 0) by lia. subst n. destruct fuel; reflexivity.
  - assert (Hn_pos : n > 0) by lia.
    assert (Hfuel_n : Z.to_nat n <> 0%nat).
    { intro H0. assert (n = 0). { apply Z2Nat.inj; [lia | lia | rewrite H0; reflexivity]. } lia. }
    assert (Hfuel_pos : fuel <> 0%nat) by lia.
    assert (Hfuel_S : fuel = S (Nat.pred fuel)).
    { destruct fuel; [contradiction Hfuel_pos; reflexivity | reflexivity]. }
    rewrite Hfuel_S.
    rewrite (Z_to_nat_S_pred n Hn Hfuel_n).
    rewrite tail_odd_prod_fuel_step by lia.
    rewrite tail_odd_prod_fuel_step by lia.
    destruct (Z.odd (Z.rem n 10)) eqn:Hodd.
    + assert (Hn10 : 0 <= Z.quot n 10) by (apply Z.quot_pos; lia).
      assert (Hfuel10_fuel : (Z.to_nat (Z.quot n 10) <= Nat.pred fuel)%nat).
      { rewrite Z_to_nat_quot by lia. apply Nat.le_trans with (m := (fuel / 10)%nat).
        - apply Nat.div_le_mono; lia.
        - rewrite Hfuel_S. apply S_div_10_le. }
      assert (Hfuel10_pred : (Z.to_nat (Z.quot n 10) <= Nat.pred (Z.to_nat n))%nat).
      { rewrite Z_to_nat_quot by lia. rewrite (Z_to_nat_S_pred n Hn Hfuel_n). apply S_div_10_le. }
      assert (Hzwf : Zwf 0 (Z.quot n 10) n).
      { unfold Zwf. split; [lia | apply (Z.quot_lt n 10); lia]. }
      assert (Hrec_fuel : tail_odd_prod_fuel (Nat.pred fuel) (Z.quot n 10) (prod * (Z.rem n 10)) 1 = tail_odd_prod_fuel (Z.to_nat (Z.quot n 10)) (Z.quot n 10) (prod * (Z.rem n 10)) 1).
      { apply (IHn (Z.quot n 10) Hzwf (Nat.pred fuel) (prod * (Z.rem n 10)) 1 Hn10 Hfuel10_fuel). }
      assert (Hrec_pred : tail_odd_prod_fuel (Nat.pred (Z.to_nat n)) (Z.quot n 10) (prod * (Z.rem n 10)) 1 = tail_odd_prod_fuel (Z.to_nat (Z.quot n 10)) (Z.quot n 10) (prod * (Z.rem n 10)) 1).
      { apply (IHn (Z.quot n 10) Hzwf (Nat.pred (Z.to_nat n)) (prod * (Z.rem n 10)) 1 Hn10 Hfuel10_pred). }
      rewrite Hrec_fuel. rewrite Hrec_pred. reflexivity.
    + assert (Hn10 : 0 <= Z.quot n 10) by (apply Z.quot_pos; lia).
      assert (Hfuel10_fuel : (Z.to_nat (Z.quot n 10) <= Nat.pred fuel)%nat).
      { rewrite Z_to_nat_quot by lia. apply Nat.le_trans with (m := (fuel / 10)%nat).
        - apply Nat.div_le_mono; lia.
        - rewrite Hfuel_S. apply S_div_10_le. }
      assert (Hfuel10_pred : (Z.to_nat (Z.quot n 10) <= Nat.pred (Z.to_nat n))%nat).
      { rewrite Z_to_nat_quot by lia. rewrite (Z_to_nat_S_pred n Hn Hfuel_n). apply S_div_10_le. }
      assert (Hzwf : Zwf 0 (Z.quot n 10) n).
      { unfold Zwf. split; [lia | apply (Z.quot_lt n 10); lia]. }
      assert (Hrec_fuel : tail_odd_prod_fuel (Nat.pred fuel) (Z.quot n 10) prod has = tail_odd_prod_fuel (Z.to_nat (Z.quot n 10)) (Z.quot n 10) prod has).
      { apply (IHn (Z.quot n 10) Hzwf (Nat.pred fuel) prod has Hn10 Hfuel10_fuel). }
      assert (Hrec_pred : tail_odd_prod_fuel (Nat.pred (Z.to_nat n)) (Z.quot n 10) prod has = tail_odd_prod_fuel (Z.to_nat (Z.quot n 10)) (Z.quot n 10) prod has).
      { apply (IHn (Z.quot n 10) Hzwf (Nat.pred (Z.to_nat n)) prod has Hn10 Hfuel10_pred). }
      rewrite Hrec_fuel. rewrite Hrec_pred. reflexivity.
Qed.
Lemma digits_state_odd_step :
  forall n prod has,
    n > 0 ->
    Z.odd (Z.rem n 10) = true ->
    digits_state n prod has = digits_state (Z.quot n 10) (prod * (Z.rem n 10)) 1.
Proof.
  intros. unfold digits_state.
  destruct (Z.to_nat n) eqn:Hfuel.
  - assert (n = 0). { apply Z2Nat.inj; [lia | lia | rewrite Hfuel; reflexivity]. } lia.
  - assert (Hstep : tail_odd_prod_fuel (S n0) n prod has = tail_odd_prod_fuel n0 (Z.quot n 10) (prod * (Z.rem n 10)) 1).
    { simpl. destruct (Z.leb_spec n 0); try lia. rewrite H0. reflexivity. }
    rewrite Hstep.
    assert (Hn10 : 0 <= Z.quot n 10) by (apply Z.quot_pos; lia).
    assert (Hfuel10 : (Z.to_nat (Z.quot n 10) <= n0)%nat).
    { rewrite Z_to_nat_quot by lia. rewrite Hfuel. apply S_div_10_le. }
    rewrite (tail_odd_prod_fuel_sufficient n0 (Z.quot n 10) (prod * (Z.rem n 10)) 1 Hn10 Hfuel10).
    reflexivity.
Qed.
Lemma digits_state_even_step :
  forall n prod has,
    n > 0 ->
    Z.odd (Z.rem n 10) = false ->
    digits_state n prod has = digits_state (Z.quot n 10) prod has.
Proof.
  intros. unfold digits_state.
  destruct (Z.to_nat n) eqn:Hfuel.
  - assert (n = 0). { apply Z2Nat.inj; [lia | lia | rewrite Hfuel; reflexivity]. } lia.
  - assert (Hstep : tail_odd_prod_fuel (S n0) n prod has = tail_odd_prod_fuel n0 (Z.quot n 10) prod has).
    { simpl. destruct (Z.leb_spec n 0); try lia. rewrite H0. reflexivity. }
    rewrite Hstep.
    assert (Hn10 : 0 <= Z.quot n 10) by (apply Z.quot_pos; lia).
    assert (Hfuel10 : (Z.to_nat (Z.quot n 10) <= n0)%nat).
    { rewrite Z_to_nat_quot by lia. rewrite Hfuel. apply S_div_10_le. }
    rewrite (tail_odd_prod_fuel_sufficient n0 (Z.quot n 10) prod has Hn10 Hfuel10).
    reflexivity.
Qed.
Lemma rem2_odd (x : Z) :
  0 <= x -> Z.odd x = true <-> Z.rem x 2 = 1.
Proof.
  intros Hx. rewrite Z.rem_mod_nonneg by lia. rewrite Zmod_odd.
  split.
  - intro H. rewrite H. reflexivity.
  - destruct (Z.odd x); simpl; intro H; [reflexivity | discriminate H].
Qed.
Lemma rem2_even (x : Z) :
  0 <= x -> Z.odd x = false <-> Z.rem x 2 <> 1.
Proof.
  intros Hx. rewrite Z.rem_mod_nonneg by lia. rewrite Zmod_odd.
  split.
  - intro H. rewrite H. discriminate.
  - destruct (Z.odd x); simpl; intro H; [contradict H; reflexivity | reflexivity].
Qed.
Lemma odd_mod10 (n : Z) :
  n > 0 -> Z.rem (Z.rem n 10) 2 = 1 -> Z.odd (Z.rem n 10) = true.
Proof.
  intros. apply rem2_odd. - apply Z.rem_bound_pos; lia. - assumption.
Qed.
Lemma even_mod10 (n : Z) :
  n > 0 -> Z.rem (Z.rem n 10) 2 <> 1 -> Z.odd (Z.rem n 10) = false.
Proof.
  intros. apply rem2_even. - apply Z.rem_bound_pos; lia. - assumption.
Qed.
Lemma odd_digit_ge1 (d : Z) :
  0 <= d < 10 -> Z.odd d = true -> 1 <= d.
Proof.
  intros Hlt Hodd. assert (d <> 0). { intro H0. rewrite H0 in Hodd. discriminate Hodd. }
  lia.
Qed.
Lemma digits_state_odd_step' :
  forall n prod has,
    n > 0 ->
    Z.rem (Z.rem n 10) 2 = 1 ->
    digits_state n prod has = digits_state (Z.quot n 10) (prod * (Z.rem n 10)) 1.
Proof.
  intros. apply digits_state_odd_step. - lia. - apply odd_mod10; assumption.
Qed.
Lemma digits_state_even_step' :
  forall n prod has,
    n > 0 ->
    Z.rem (Z.rem n 10) 2 <> 1 ->
    digits_state n prod has = digits_state (Z.quot n 10) prod has.
Proof.
  intros. apply digits_state_even_step. - lia. - apply even_mod10; assumption.
Qed.
Lemma digits_state_ge_prod :
  forall n prod,
    0 <= n ->
    1 <= prod ->
    prod <= digits_state n prod 1.
Proof.
  enough (forall fuel n prod, Z.to_nat n = fuel -> 0 <= n -> 1 <= prod -> prod <= digits_state n prod 1).
  { intros; eauto. }
  intros fuel.
  induction fuel as [fuel IHfuel] using (well_founded_induction_type lt_wf).
  intros n prod Hfuel Hn Hprod.
  destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
  - subst n. unfold digits_state. simpl. lia.
  - assert (Hn_pos : n > 0) by lia.
    unfold digits_state.
    destruct (Z.to_nat n) eqn:Hfuel_n.
    + assert (n = 0). { apply Z2Nat.inj; [lia | lia | rewrite Hfuel_n; reflexivity]. } lia.
    + simpl tail_odd_prod_fuel.
      destruct (Z.leb_spec n 0).
      * lia.
      * destruct (Z.odd (Z.rem n 10)) eqn:Hodd.
        -- assert (Hn10 : 0 <= Z.quot n 10) by (apply Z.quot_pos; lia).
           assert (Hfuel10_lt : (Z.to_nat (Z.quot n 10) < fuel)%nat).
           { rewrite Z_to_nat_quot by lia. rewrite <- Hfuel. apply Nat.div_lt_upper_bound; lia. }
           assert (Hfuel10_le : (Z.to_nat (Z.quot n 10) <= n0)%nat) by lia.
           assert (Hprod_d : 1 <= prod * (Z.rem n 10)).
           { assert (Hbound : 0 <= Z.rem n 10 < 10) by (apply Z.rem_bound_pos; lia).
             assert (Hneq : Z.rem n 10 <> 0). { intro H0. rewrite H0 in Hodd. discriminate Hodd. }
             lia. }
           rewrite (tail_odd_prod_fuel_sufficient n0 (Z.quot n 10) (prod * (Z.rem n 10)) 1 Hn10 Hfuel10_le).
           specialize (IHfuel (Z.to_nat (Z.quot n 10)) Hfuel10_lt (Z.quot n 10) (prod * (Z.rem n 10)) eq_refl Hn10 Hprod_d).
           unfold digits_state in IHfuel.
           assert (Hdig : 1 <= Z.rem n 10).
           { assert (Hbound : 0 <= Z.rem n 10 < 10) by (apply Z.rem_bound_pos; lia).
             assert (Hneq : Z.rem n 10 <> 0). { intro H0. rewrite H0 in Hodd. discriminate Hodd. }
             lia. }
           nia.
        -- assert (Hn10 : 0 <= Z.quot n 10) by (apply Z.quot_pos; lia).
           assert (Hfuel10_lt : (Z.to_nat (Z.quot n 10) < fuel)%nat).
           { rewrite Z_to_nat_quot by lia. rewrite <- Hfuel. apply Nat.div_lt_upper_bound; lia. }
           assert (Hfuel10_le : (Z.to_nat (Z.quot n 10) <= n0)%nat) by lia.
           rewrite (tail_odd_prod_fuel_sufficient n0 (Z.quot n 10) prod 1 Hn10 Hfuel10_le).
           specialize (IHfuel (Z.to_nat (Z.quot n 10)) Hfuel10_lt (Z.quot n 10) prod eq_refl Hn10 Hprod).
           unfold digits_state in IHfuel.
           lia.
Qed.
Lemma digits_state_odd_prod_le :
  forall n prod,
    n > 0 ->
    Z.rem (Z.rem n 10) 2 = 1 ->
    1 <= prod ->
    prod * (Z.rem n 10) <= digits_state n prod 1.
Proof.
  intros.
  rewrite (digits_state_odd_step n prod 1).
  - apply digits_state_ge_prod.
    + apply Z.quot_pos; lia.
    + assert (H1d : 1 <= Z.rem n 10).
      { apply odd_digit_ge1; [apply Z.rem_bound_pos; lia | apply odd_mod10; assumption]. }
      nia.
  - lia.
  - apply odd_mod10; assumption.
Qed.
Lemma prod_odd_digit_le_state n prod has :
  n > 0 ->
  Z.rem (Z.rem n 10) 2 = 1 ->
  1 <= prod ->
  prod * (Z.rem n 10) <= digits_state n prod has.
Proof.
  intros Hn Hodd Hprod.
  assert (Hodd' : Z.odd (Z.rem n 10) = true) by (apply odd_mod10; assumption).
  rewrite (digits_state_odd_step n prod has) by assumption.
  apply digits_state_ge_prod.
  - apply Z.quot_pos; lia.
  - assert (H1d : 1 <= Z.rem n 10).
    { apply odd_digit_ge1; [apply Z.rem_bound_pos; lia | assumption]. }
    nia.
Qed.


Ltac solve_p131_pure :=
  intros;
  repeat match goal with |- _ |-- “ _ ” => apply derivable1s_coq_prop_r end;
  try unfold problem_131_spec in *;
  try fold digits_state in *;
  try fold tail_odd_prod in *;
  try subst;
  try match goal with
      | Hodd : Z.rem (Z.rem ?n 10) 2 = 1,
        Hprod : 1 <= ?prod |- 1 <= ?prod * Z.rem ?n 10 =>
        assert (1 <= Z.rem n 10)
          by (apply odd_digit_ge1; [apply Z.rem_bound_pos; lia | apply odd_mod10; assumption]);
        nia
      end;
  try match goal with
      | Hstate : digits_state (Z.quot ?n 10) (?prod * Z.rem ?n 10) 1 <= INT_MAX,
        Hodd : Z.rem (Z.rem ?n 10) 2 = 1,
        Hprod : 1 <= ?prod |- ?prod * Z.rem ?n 10 <= INT_MAX =>
        assert (1 <= prod * Z.rem n 10) by
          (assert (1 <= Z.rem n 10)
             by (apply odd_digit_ge1; [apply Z.rem_bound_pos; lia | apply odd_mod10; assumption]);
           nia);
        assert (prod * Z.rem n 10 <= digits_state (Z.quot n 10) (prod * Z.rem n 10) 1)
          by (apply digits_state_ge_prod; [apply Z.quot_pos; lia | nia]);
        lia
      end;
  try match goal with
      | n : Z |- _ =>
        assert (0 <= Z.quot n 10 <= n)
          by (split; [apply Z.quot_pos; lia | apply Zlt_le_weak; apply Z.quot_lt; lia])
      end;
  try match goal with
      | Heq : context [digits_state ?n ?prod ?has] |- prod * Z.rem ?n 10 <= INT_MAX =>
        assert (prod * Z.rem n 10 <= digits_state n prod has)
          by (apply prod_odd_digit_le_state; [lia | assumption | assumption]);
        lia
      | Heq : context [digits_state ?n ?prod ?has] |- 1 <= prod * Z.rem ?n 10 =>
        assert (1 <= Z.rem n 10)
          by (apply odd_digit_ge1; [apply Z.rem_bound_pos; lia | apply odd_mod10; assumption]);
        nia
      end;
  try match goal with
      | Heq : tail_odd_prod ?n0 = digits_state ?n ?prod ?has,
        Hodd : Z.rem (Z.rem ?n 10) 2 = 1 |- _ =>
        assert (Hstep : digits_state n prod has = digits_state (Z.quot n 10) (prod * Z.rem n 10) 1)
          by (apply digits_state_odd_step'; [lia | assumption]);
        rewrite Hstep in *; clear Hstep
      | Heq : tail_odd_prod ?n0 = digits_state ?n ?prod ?has,
        Heven : Z.rem (Z.rem ?n 10) 2 <> 1 |- _ =>
        assert (Hstep : digits_state n prod has = digits_state (Z.quot n 10) prod has)
          by (apply digits_state_even_step'; [lia | assumption]);
        rewrite Hstep in *; clear Hstep
      end;
  try match goal with
      | n : Z |- _ =>
        assert (n = 0) by lia; subst n; simpl in *
      end;
  try reflexivity;
  try lia;
  try nia;
  try tauto.

Lemma proof_of_p131_digits_entail_wit_1 : p131_digits_entail_wit_1.
Proof.
  pre_process.
  Right.
  Exists n_pre.
  split_pure_spatial.
  - cancel emp.
  - split_pures; solve_p131_pure.
Qed.

Lemma proof_of_p131_digits_entail_wit_2_1 : p131_digits_entail_wit_2_1.
Proof.
  pre_process.
  Left.
  Exists n_pre.
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    all: try solve_p131_pure.
    assert (1 <= prod * Z.rem n 10).
    { assert (1 <= Z.rem n 10)
        by (apply odd_digit_ge1; [apply Z.rem_bound_pos; lia | apply odd_mod10; assumption]).
      nia.
    }
    assert (prod * Z.rem n 10 <= digits_state (Z.quot n 10) (prod * Z.rem n 10) 1).
    { apply digits_state_ge_prod.
      - apply Z.quot_pos; lia.
      - nia.
    }
    lia.
Qed.

Lemma proof_of_p131_digits_entail_wit_2_2 : p131_digits_entail_wit_2_2.
Proof.
  pre_process.
  Left.
  Exists n_pre.
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    all: try solve_p131_pure.
    assert (1 <= prod * Z.rem n 10).
    { assert (1 <= Z.rem n 10)
        by (apply odd_digit_ge1; [apply Z.rem_bound_pos; lia | apply odd_mod10; assumption]).
      nia.
    }
    assert (prod * Z.rem n 10 <= digits_state (Z.quot n 10) (prod * Z.rem n 10) 1).
    { apply digits_state_ge_prod.
      - apply Z.quot_pos; lia.
      - nia.
    }
    lia.
Qed.

Lemma proof_of_p131_digits_entail_wit_2_3 : p131_digits_entail_wit_2_3.
Proof.
  pre_process.
  Left.
  Exists n_pre.
  split_pure_spatial.
  - cancel emp.
  - split_pures; solve_p131_pure.
Qed.

Lemma proof_of_p131_digits_entail_wit_2_4 : p131_digits_entail_wit_2_4.
Proof.
  pre_process.
  Right.
  Exists n_pre.
  split_pure_spatial.
  - cancel emp.
  - split_pures; solve_p131_pure.
Qed.

Lemma proof_of_p131_digits_return_wit_1 : p131_digits_return_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    all: try solve_p131_pure.
    split.
    + lia.
    + unfold tail_odd_prod, digits_state in H8.
      simpl in H8.
      exact (eq_sym H8).
Qed.

Lemma proof_of_p131_digits_return_wit_2 : p131_digits_return_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    all: try solve_p131_pure.
    split.
    + lia.
    + unfold tail_odd_prod, digits_state in H8.
      simpl in H8.
      exact (eq_sym H8).
Qed.

Lemma proof_of_p131_digits_safety_wit_19 : p131_digits_safety_wit_19.
Proof.
  pre_process.
  split_pures.
  - solve_p131_pure.
    assert (1 <= prod * Z.rem n 10).
    { assert (1 <= Z.rem n 10)
        by (apply odd_digit_ge1; [apply Z.rem_bound_pos; lia | apply odd_mod10; assumption]).
      nia.
    }
    assert (prod * Z.rem n 10 <= digits_state (Z.quot n 10) (prod * Z.rem n 10) 1).
    { apply digits_state_ge_prod.
      - apply Z.quot_pos; lia.
      - nia.
    }
    lia.
  - solve_p131_pure.
    assert (1 <= prod * Z.rem n 10).
    { assert (1 <= Z.rem n 10)
        by (apply odd_digit_ge1; [apply Z.rem_bound_pos; lia | apply odd_mod10; assumption]).
      nia.
    }
    lia.
Qed.

Lemma proof_of_p131_digits_safety_wit_20 : p131_digits_safety_wit_20.
Proof.
  pre_process.
  split_pures.
  - solve_p131_pure.
    assert (1 <= prod * Z.rem n 10).
    { assert (1 <= Z.rem n 10)
        by (apply odd_digit_ge1; [apply Z.rem_bound_pos; lia | apply odd_mod10; assumption]).
      nia.
    }
    assert (prod * Z.rem n 10 <= digits_state (Z.quot n 10) (prod * Z.rem n 10) 1).
    { apply digits_state_ge_prod.
      - apply Z.quot_pos; lia.
      - nia.
    }
    lia.
  - solve_p131_pure.
    assert (1 <= prod * Z.rem n 10).
    { assert (1 <= Z.rem n 10)
        by (apply odd_digit_ge1; [apply Z.rem_bound_pos; lia | apply odd_mod10; assumption]).
      nia.
    }
    lia.
Qed.

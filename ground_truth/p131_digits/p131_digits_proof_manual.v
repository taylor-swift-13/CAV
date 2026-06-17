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
From SimpleC.EE.CAV.ground_truth_p131_digits Require Import p131_digits_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p131_digits.
Local Open Scope sac.

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

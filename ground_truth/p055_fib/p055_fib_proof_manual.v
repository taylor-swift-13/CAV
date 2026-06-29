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
From SimpleC.EE.CAV.ground_truth_p055_fib Require Import p055_fib_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Init.Nat.

Import naive_C_Rules.
Require Import p055_fib.
Local Open Scope sac.
Require Import Coq.micromega.Lia.

Local Open Scope list_scope.

(* Proof helpers moved from p055_fib.v so public contract files expose definitions only. *)

Lemma fib_seq_0 :
  fib_seq 0 = 0.
Proof. reflexivity. Qed.
Lemma fib_seq_1 :
  fib_seq 1 = 1.
Proof. reflexivity. Qed.
Lemma fib_seq_step : forall i,
  2 <= i ->
  fib_seq i = fib_seq (i - 2) + fib_seq (i - 1).
Proof.
  intros i Hi.
  unfold fib_seq.
  assert (Hi0: Z.to_nat i = S (S (Z.to_nat (i - 2)))).
  { apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite !Nat2Z.inj_succ.
    rewrite Z2Nat.id by lia.
    lia. }
  assert (Hi1: Z.to_nat (i - 1) = S (Z.to_nat (i - 2))).
  { apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite !Nat2Z.inj_succ.
    rewrite Z2Nat.id by lia.
    lia. }
  rewrite Hi0, Hi1.
  simpl.
  lia.
Qed.
Lemma problem_55_spec_of_fib_seq : forall n res,
  0 <= n ->
  res = fib_seq n ->
  problem_55_spec n res.
Proof.
  intros n res Hn Hres.
  unfold problem_55_spec.
  auto.
Qed.


Lemma proof_of_p055_fib_safety_wit_4 : p055_fib_safety_wit_4.
Proof.
  pre_process.
  subst a b.
  match goal with
  | H: fib_step_int_range n_pre |- _ =>
      unfold fib_step_int_range in H;
      specialize (H i)
  end.
  assert (Hr : 2 <= i <= n_pre) by lia.
  match goal with
  | H: (2 <= i <= n_pre -> _) |- _ =>
      specialize (H Hr)
  end.
  andp_cancel; lia.
Qed.

Lemma proof_of_p055_fib_entail_wit_1 : p055_fib_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_p055_fib_entail_wit_2 : p055_fib_entail_wit_2.
Proof.
  pre_process.
  assert (Hstep : a + b = fib_seq i).
  {
    subst a b.
    replace (fib_seq i) with (fib_seq (i - 2) + fib_seq (i - 1))
      by (symmetry; apply fib_seq_step; lia).
    reflexivity.
  }
  assert (Hbnext : b = fib_seq (i + 1 - 2)).
  { subst b. replace (i + 1 - 2) with (i - 1) by lia. reflexivity. }
  assert (Hcnext : a + b = fib_seq (i + 1 - 1)).
  { replace (i + 1 - 1) with i by lia. exact Hstep. }
  andp_cancel; auto; try lia.
  sep_apply store_int_undef_store_int.
  andp_cancel.
Qed.

Lemma proof_of_p055_fib_return_wit_1 : p055_fib_return_wit_1.
Proof.
  pre_process.
  subst b.
  andp_cancel; auto.
  apply problem_55_spec_of_fib_seq.
  - lia.
  - replace (i - 1) with n_pre by lia.
    reflexivity.
Qed.

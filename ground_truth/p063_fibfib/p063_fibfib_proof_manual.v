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
From SimpleC.EE.CAV.ground_truth_p063_fibfib Require Import p063_fibfib_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Init.Nat.

Import naive_C_Rules.
Require Import p063_fibfib.
Local Open Scope sac.
Require Import Coq.micromega.Lia.

Local Open Scope list_scope.

(* Proof helpers moved from p063_fibfib.v so public contract files expose definitions only. *)

Lemma fibfib_0 :
  fibfib 0 = 0.
Proof. reflexivity. Qed.
Lemma fibfib_1 :
  fibfib 1 = 0.
Proof. reflexivity. Qed.
Lemma fibfib_2 :
  fibfib 2 = 1.
Proof. reflexivity. Qed.
Lemma fibfib_step : forall i,
  3 <= i ->
  fibfib i =
    fibfib (i - 1) + fibfib (i - 2) + fibfib (i - 3).
Proof.
  intros i Hi.
  unfold fibfib.
  assert (Hi0: Z.to_nat i = S (S (S (Z.to_nat (i - 3))))).
  { apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite !Nat2Z.inj_succ.
    rewrite Z2Nat.id by lia.
    lia. }
  assert (Hi1: Z.to_nat (i - 1) = S (S (Z.to_nat (i - 3)))).
  { apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite !Nat2Z.inj_succ.
    rewrite Z2Nat.id by lia.
    lia. }
  assert (Hi2: Z.to_nat (i - 2) = S (Z.to_nat (i - 3))).
  { apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite !Nat2Z.inj_succ.
    rewrite Z2Nat.id by lia.
    lia. }
  rewrite Hi0, Hi1, Hi2.
  simpl.
  lia.
Qed.
Lemma problem_63_spec_of_fibfib : forall n res,
  0 <= n ->
  res = fibfib n ->
  problem_63_spec n res.
Proof.
  intros n res Hn Hres.
  unfold problem_63_spec.
  auto.
Qed.
Lemma problem_63_spec_base_0 :
  problem_63_spec 0 0.
Proof.
  apply problem_63_spec_of_fibfib.
  - lia.
  - rewrite fibfib_0. reflexivity.
Qed.
Lemma problem_63_spec_base_1 :
  problem_63_spec 1 0.
Proof.
  apply problem_63_spec_of_fibfib.
  - lia.
  - rewrite fibfib_1. reflexivity.
Qed.
Lemma problem_63_spec_base_2 :
  problem_63_spec 2 1.
Proof.
  apply problem_63_spec_of_fibfib.
  - lia.
  - rewrite fibfib_2. reflexivity.
Qed.


Lemma proof_of_p063_fibfib_safety_wit_11 : p063_fibfib_safety_wit_11.
Proof.
  pre_process.
  subst a b c.
  match goal with
  | Hrange0: fibfib_step_int_range n_pre |- _ =>
      unfold fibfib_step_int_range in Hrange0;
      pose proof (Hrange0 i) as Hrange;
      clear Hrange0
  end.
  assert (Hr : 3 <= i <= n_pre) by lia.
  specialize (Hrange Hr).
  destruct Hrange as [_ Hsum].
  andp_cancel; lia.
Qed.

Lemma proof_of_p063_fibfib_safety_wit_12 : p063_fibfib_safety_wit_12.
Proof.
  pre_process.
  subst a b c.
  match goal with
  | H: fibfib_step_int_range n_pre |- _ =>
      unfold fibfib_step_int_range in H;
      pose proof (H i) as Hrange;
      clear H
  end.
  assert (Hr : 3 <= i <= n_pre) by lia.
  specialize (Hrange Hr).
  destruct Hrange as [Hsum _].
  andp_cancel; lia.
Qed.

Lemma proof_of_p063_fibfib_entail_wit_1 : p063_fibfib_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_p063_fibfib_entail_wit_2 : p063_fibfib_entail_wit_2.
Proof.
  pre_process.
  assert (Hstep : (a + b) + c = fibfib i).
  {
    subst a b c.
    replace (fibfib i) with
      (fibfib (i - 1) + fibfib (i - 2) + fibfib (i - 3))
      by (symmetry; apply fibfib_step; lia).
    lia.
  }
  assert (Hbnext : b = fibfib (i + 1 - 3)).
  { subst b. replace (i + 1 - 3) with (i - 2) by lia. reflexivity. }
  assert (Hcnext : c = fibfib (i + 1 - 2)).
  { subst c. replace (i + 1 - 2) with (i - 1) by lia. reflexivity. }
  assert (Hnext : (a + b) + c = fibfib (i + 1 - 1)).
  { replace (i + 1 - 1) with i by lia. exact Hstep. }
  andp_cancel; auto; try lia.
  sep_apply store_int_undef_store_int.
  andp_cancel.
Qed.

Lemma proof_of_p063_fibfib_return_wit_1 : p063_fibfib_return_wit_1.
Proof.
  pre_process.
  subst c.
  andp_cancel; auto.
  apply problem_63_spec_of_fibfib.
  - lia.
  - replace (i - 1) with n_pre by lia.
    reflexivity.
Qed.

Lemma proof_of_p063_fibfib_return_wit_2 : p063_fibfib_return_wit_2.
Proof.
  pre_process.
  andp_cancel; auto.
  subst n_pre.
  apply problem_63_spec_base_2.
Qed.

Lemma proof_of_p063_fibfib_return_wit_3 : p063_fibfib_return_wit_3.
Proof.
  pre_process.
  andp_cancel; auto.
  subst n_pre.
  apply problem_63_spec_base_1.
Qed.

Lemma proof_of_p063_fibfib_return_wit_4 : p063_fibfib_return_wit_4.
Proof.
  pre_process.
  andp_cancel; auto.
  subst n_pre.
  apply problem_63_spec_base_0.
Qed.

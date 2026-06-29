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
From SimpleC.EE.CAV.ground_truth_p046_fib4 Require Import p046_fib4_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Arith.Arith.

Import naive_C_Rules.
Require Import p046_fib4.
Local Open Scope sac.
Require Import Coq.micromega.Lia.

Local Open Scope list_scope.

(* Proof helpers moved from p046_fib4.v so public contract files expose definitions only. *)

Lemma fib4_fuel_nat :
  forall (n fuel : nat),
    (n <= fuel)%nat ->
    fib4_fuel fuel (Z.of_nat n) = Z.of_nat (fib4_nat n).
Proof.
  apply (well_founded_induction
           lt_wf
           (fun m => forall fuel : nat,
              (m <= fuel)%nat ->
              fib4_fuel fuel (Z.of_nat m) = Z.of_nat (fib4_nat m))).
  intros m IH fuel Hle.
  destruct fuel as [| fuel]; [destruct m; [reflexivity | lia] |].
  destruct m as [| [| [| [| n]]]]; cbn [fib4_fuel fib4_nat]; try reflexivity.
  remember (Z.of_nat (S (S (S (S n))))) as z eqn:Hz.
  change
    (fib4_fuel (S fuel) z =
     Z.of_nat (fib4_nat (S (S (S n))) + fib4_nat (S (S n)) +
               fib4_nat (S n) + fib4_nat n)).
  cbn [fib4_fuel fib4_nat].
  assert (Hz0 : (z =? 0)%Z = false) by (apply Z.eqb_neq; subst z; lia).
  assert (Hz1 : (z =? 1)%Z = false) by (apply Z.eqb_neq; subst z; lia).
  assert (Hz2 : (z =? 2)%Z = false) by (apply Z.eqb_neq; subst z; lia).
  assert (Hz3 : (z =? 3)%Z = false) by (apply Z.eqb_neq; subst z; lia).
  rewrite Hz0, Hz1, Hz2, Hz3.
  replace (z - 1) with (Z.of_nat (S (S (S n)))) by (subst z; lia).
  replace (z - 2) with (Z.of_nat (S (S n))) by (subst z; lia).
  replace (z - 3) with (Z.of_nat (S n)) by (subst z; lia).
  replace (z - 4) with (Z.of_nat n) by (subst z; lia).
  rewrite (IH (S (S (S n))) ltac:(lia) fuel ltac:(lia)).
  rewrite (IH (S (S n)) ltac:(lia) fuel ltac:(lia)).
  rewrite (IH (S n) ltac:(lia) fuel ltac:(lia)).
  rewrite (IH n ltac:(lia) fuel ltac:(lia)).
  simpl fib4_nat.
  repeat rewrite Nat2Z.inj_add.
  reflexivity.
Qed.
Lemma fib4_original_spec :
  forall n, 0 <= n -> fib4 n = Z.of_nat (fib4_nat (Z.to_nat n)).
Proof.
  intros n Hn.
  unfold fib4.
  replace (fib4_fuel (Z.to_nat n) n) with
    (fib4_fuel (Z.to_nat n) (Z.of_nat (Z.to_nat n))).
  2:{ rewrite Z2Nat.id by lia. reflexivity. }
  apply fib4_fuel_nat.
  lia.
Qed.
Lemma fib4_recurrence :
  forall n, 4 <= n ->
    fib4 n = fib4 (n - 1) + fib4 (n - 2) + fib4 (n - 3) + fib4 (n - 4).
Proof.
  intros n Hn.
  rewrite !fib4_original_spec by lia.
  replace (Z.to_nat (n - 1)) with (Z.to_nat n - 1)%nat by lia.
  replace (Z.to_nat (n - 2)) with (Z.to_nat n - 2)%nat by lia.
  replace (Z.to_nat (n - 3)) with (Z.to_nat n - 3)%nat by lia.
  replace (Z.to_nat (n - 4)) with (Z.to_nat n - 4)%nat by lia.
  assert (Hnat_ge : (4 <= Z.to_nat n)%nat) by lia.
  destruct (Z.to_nat n) as [| [| [| [| k]]]]; try lia.
  replace (S (S (S (S k))) - 1)%nat with (S (S (S k))) by lia.
  replace (S (S (S (S k))) - 2)%nat with (S (S k)) by lia.
  replace (S (S (S (S k))) - 3)%nat with (S k) by lia.
  replace (S (S (S (S k))) - 4)%nat with k by lia.
  simpl fib4_nat.
  repeat rewrite Nat2Z.inj_add.
  lia.
Qed.
Lemma problem_46_spec_base_0 :
  problem_46_spec 0 0.
Proof.
  unfold problem_46_spec, fib4. simpl. lia.
Qed.
Lemma problem_46_spec_base_1 :
  problem_46_spec 1 0.
Proof.
  unfold problem_46_spec, fib4. simpl. lia.
Qed.
Lemma problem_46_spec_base_2 :
  problem_46_spec 2 2.
Proof.
  unfold problem_46_spec, fib4. simpl. lia.
Qed.
Lemma problem_46_spec_base_3 :
  problem_46_spec 3 0.
Proof.
  unfold problem_46_spec, fib4. simpl. lia.
Qed.


Lemma proof_of_p046_fib4_safety_wit_14 : p046_fib4_safety_wit_14.
Proof.
  pre_process.
  subst a b c d.
  unfold fib4_step_int_range in H4.
  assert (Hr : 4 <= i <= n_pre) by lia.
  specialize (H4 i Hr).
  destruct H4 as [_ [_ Hsum]].
  andp_cancel; lia.
Qed.

Lemma proof_of_p046_fib4_safety_wit_15 : p046_fib4_safety_wit_15.
Proof.
  pre_process.
  subst a b c d.
  unfold fib4_step_int_range in H4.
  assert (Hr : 4 <= i <= n_pre) by lia.
  specialize (H4 i Hr).
  destruct H4 as [_ [Hsum _]].
  andp_cancel; lia.
Qed.

Lemma proof_of_p046_fib4_safety_wit_16 : p046_fib4_safety_wit_16.
Proof.
  pre_process.
  subst a b c d.
  unfold fib4_step_int_range in H4.
  assert (Hr : 4 <= i <= n_pre) by lia.
  specialize (H4 i Hr).
  destruct H4 as [Hsum _].
  andp_cancel; lia.
Qed.

Lemma proof_of_p046_fib4_entail_wit_1 : p046_fib4_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_p046_fib4_entail_wit_2 : p046_fib4_entail_wit_2.
Proof.
  pre_process.
  assert (Hstep:
    ((a + b) + c) + d = fib4 i).
  {
    subst a b c d.
    replace (fib4 i) with
      (fib4 (i - 1) + fib4 (i - 2) +
       fib4 (i - 3) + fib4 (i - 4))
      by (symmetry; apply fib4_recurrence; lia).
    lia.
  }
  assert (Hbnext : b = fib4 (i + 1 - 4)).
  { subst b. replace (i + 1 - 4) with (i - 3) by lia. reflexivity. }
  assert (Hcnext : c = fib4 (i + 1 - 3)).
  { subst c. replace (i + 1 - 3) with (i - 2) by lia. reflexivity. }
  assert (Hdnext : d = fib4 (i + 1 - 2)).
  { subst d. replace (i + 1 - 2) with (i - 1) by lia. reflexivity. }
  assert (Hnext : ((a + b) + c) + d = fib4 (i + 1 - 1)).
  { replace (i + 1 - 1) with i by lia. exact Hstep. }
  andp_cancel; auto; try lia.
  sep_apply store_int_undef_store_int.
  andp_cancel.
Qed.

Lemma proof_of_p046_fib4_return_wit_1 : p046_fib4_return_wit_1.
Proof.
  pre_process.
  subst d.
  andp_cancel; auto; try lia.
  replace n_pre with (i - 1) by lia.
  unfold problem_46_spec.
  split; [lia | reflexivity].
Qed.

Lemma proof_of_p046_fib4_return_wit_2 : p046_fib4_return_wit_2.
Proof.
  pre_process.
  andp_cancel; auto.
  subst n_pre.
  apply problem_46_spec_base_3.
Qed.

Lemma proof_of_p046_fib4_return_wit_3 : p046_fib4_return_wit_3.
Proof.
  pre_process.
  andp_cancel; auto.
  subst n_pre.
  apply problem_46_spec_base_2.
Qed.

Lemma proof_of_p046_fib4_return_wit_4 : p046_fib4_return_wit_4.
Proof.
  pre_process.
  andp_cancel; auto.
  subst n_pre.
  apply problem_46_spec_base_1.
Qed.

Lemma proof_of_p046_fib4_return_wit_5 : p046_fib4_return_wit_5.
Proof.
  pre_process.
  andp_cancel; auto.
  subst n_pre.
  apply problem_46_spec_base_0.
Qed.

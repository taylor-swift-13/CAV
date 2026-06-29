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
From SimpleC.EE.CAV.ground_truth_p139_special_factorial Require Import p139_special_factorial_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Init.Nat.

Import naive_C_Rules.
Require Import p139_special_factorial.
Local Open Scope sac.
Require Import Coq.micromega.Lia.

Local Open Scope list_scope.

(* Proof helpers moved from p139_special_factorial.v so public contract files expose definitions only. *)

Lemma factorial_0 : factorial 0 = 1.
Proof.
  reflexivity.
Qed.
Lemma bfact_coq_0 : bfact_coq 0 = 1.
Proof.
  reflexivity.
Qed.
Lemma factorial_step :
  forall i,
    1 <= i ->
    factorial (i - 1) * i = factorial i.
Proof.
  intros i Hi.
  destruct (Z.eq_dec i 1) as [-> | Hneq].
  - reflexivity.
  - assert (Hi_gt : 1 < i) by lia.
    unfold factorial.
    replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia.
    simpl.
    destruct (Z.leb_spec0 i 1); [lia | ring].
Qed.
Lemma bfact_coq_step :
  forall i,
    1 <= i ->
    bfact_coq (i - 1) * factorial i = bfact_coq i.
Proof.
  intros i Hi.
  unfold bfact_coq.
  replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia.
  simpl.
  destruct (Z.leb_spec0 i 0); [lia |].
  fold (factorial i).
  reflexivity.
Qed.


Lemma proof_of_p139_special_factorial_safety_wit_4 : p139_special_factorial_safety_wit_4.
Proof.
  unfold p139_special_factorial_safety_wit_4.
  intros.
  Intros.
  entailer!.
  all: first
       [ match goal with
         | Hfact : ?f = factorial (?ii - 1) |- _ =>
             assert (Hcases :
               ii = 1 \/ ii = 2 \/ ii = 3 \/ ii = 4 \/ ii = 5 \/ ii = 6 \/ ii = 7 \/ ii = 8) by lia;
             destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
             rewrite Hfact;
             vm_compute; congruence
         end
       | lia ].
Qed.

Lemma proof_of_p139_special_factorial_safety_wit_5 : p139_special_factorial_safety_wit_5.
Proof.
  unfold p139_special_factorial_safety_wit_5.
  intros.
  Intros.
  entailer!.
  all: first
       [ match goal with
         | Hfact : ?f = factorial (?ii - 1),
           Hbfact : ?b = bfact_coq (?ii - 1) |- _ =>
             assert (Hcases :
               ii = 1 \/ ii = 2 \/ ii = 3 \/ ii = 4 \/ ii = 5 \/ ii = 6 \/ ii = 7 \/ ii = 8) by lia;
             destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
             rewrite Hfact;
             rewrite Hbfact;
             vm_compute; congruence
         end
       | lia ].
Qed.

Lemma proof_of_p139_special_factorial_entail_wit_1 : p139_special_factorial_entail_wit_1.
Proof.
  unfold p139_special_factorial_entail_wit_1.
  intros.
  Intros.
  entailer!.
Qed.

Lemma proof_of_p139_special_factorial_entail_wit_2 : p139_special_factorial_entail_wit_2.
Proof.
  unfold p139_special_factorial_entail_wit_2.
  intros.
  Intros.
  entailer!.
  all: first
       [ match goal with
         | Hfact : ?f = factorial (?ii - 1),
           Hbfact : ?b = bfact_coq (?ii - 1) |- _ =>
             rewrite Hfact;
             rewrite Hbfact;
             rewrite (factorial_step ii) by lia;
             rewrite (bfact_coq_step ii) by lia;
             replace (ii + 1 - 1) with ii by lia;
             reflexivity
         end
       | match goal with
         | Hfact : ?f = factorial (?ii - 1) |- _ =>
             rewrite Hfact;
             rewrite (factorial_step ii) by lia;
             replace (ii + 1 - 1) with ii by lia;
             reflexivity
         end
       | lia ].
Qed.

Lemma proof_of_p139_special_factorial_return_wit_1 : p139_special_factorial_return_wit_1.
Proof.
  unfold p139_special_factorial_return_wit_1.
  intros.
  Intros.
  entailer!.
  unfold problem_139_spec.
  match goal with
  | Hgt : ?ii > ?np,
    Hle : ?ii <= ?np + 1,
    Hbfact : ?b = bfact_coq (?ii - 1) |- _ =>
      assert (Hieq : ii = np + 1) by lia;
      subst ii;
      replace ((np + 1) - 1) with np in Hbfact by lia;
      exact Hbfact
  end.
Qed.

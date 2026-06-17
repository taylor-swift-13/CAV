Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p098_count_upper Require Import p098_count_upper_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
From AUXLib Require Import ListLib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p098_count_upper.
Local Open Scope sac.

Ltac solve_upper_hit :=
  pre_process;
  repeat match goal with
  | H : ?x = count_upper_even_upto ?i ?l |- _ => subst x
  end;
  match goal with
  | |- context[count_upper_even_upto (?i + 1) ?l] =>
      repeat rewrite app_Znth1 in * by lia;
      assert (Hhit:
        Znth i l 0 = 65 \/ Znth i l 0 = 69 \/ Znth i l 0 = 73 \/
        Znth i l 0 = 79 \/ Znth i l 0 = 85) by lia;
      rewrite count_upper_even_upto_step_hit with (i := i) (l := l)
        by (try lia; try assumption; exact Hhit)
  end;
  entailer!.

Lemma proof_of_p098_count_upper_entail_wit_1 : p098_count_upper_entail_wit_1.
Proof.
  unfold p098_count_upper_entail_wit_1.
  intros.
  pre_process.
  subst retval.
  rewrite count_upper_even_upto_0.
  entailer!.
Qed.

Lemma proof_of_p098_count_upper_entail_wit_2_1 : p098_count_upper_entail_wit_2_1.
Proof.
  unfold p098_count_upper_entail_wit_2_1.
  intros.
  solve_upper_hit.
Qed.

Lemma proof_of_p098_count_upper_entail_wit_2_2 : p098_count_upper_entail_wit_2_2.
Proof.
  unfold p098_count_upper_entail_wit_2_2.
  intros.
  solve_upper_hit.
Qed.

Lemma proof_of_p098_count_upper_entail_wit_2_3 : p098_count_upper_entail_wit_2_3.
Proof.
  unfold p098_count_upper_entail_wit_2_3.
  intros.
  solve_upper_hit.
Qed.

Lemma proof_of_p098_count_upper_entail_wit_2_4 : p098_count_upper_entail_wit_2_4.
Proof.
  unfold p098_count_upper_entail_wit_2_4.
  intros.
  solve_upper_hit.
Qed.

Lemma proof_of_p098_count_upper_entail_wit_2_5 : p098_count_upper_entail_wit_2_5.
Proof.
  unfold p098_count_upper_entail_wit_2_5.
  intros.
  solve_upper_hit.
Qed.

Lemma proof_of_p098_count_upper_entail_wit_2_6 : p098_count_upper_entail_wit_2_6.
Proof.
  unfold p098_count_upper_entail_wit_2_6.
  intros.
  pre_process.
  repeat match goal with
  | H : ?x = count_upper_even_upto ?i ?l |- _ => subst x
  end.
  repeat rewrite app_Znth1 in * by lia.
  rewrite count_upper_even_upto_step_even_miss by lia.
  entailer!.
Qed.

Lemma proof_of_p098_count_upper_entail_wit_2_7 : p098_count_upper_entail_wit_2_7.
Proof.
  unfold p098_count_upper_entail_wit_2_7.
  intros.
  pre_process.
  repeat match goal with
  | H : ?x = count_upper_even_upto ?i ?l |- _ => subst x
  end.
  rewrite count_upper_even_upto_step_odd by lia.
  entailer!.
Qed.

Lemma proof_of_p098_count_upper_return_wit_1 : p098_count_upper_return_wit_1.
Proof.
  unfold p098_count_upper_return_wit_1.
  intros.
  pre_process.
  repeat match goal with
  | H : ?x = count_upper_even_upto ?i ?l |- _ => subst x
  end.
  assert (i = len) by lia.
  subst i.
  entailer!.
  apply problem_98_spec_intro.
  match goal with
  | Hlen : Zlength l = len |- _ => rewrite Hlen
  end.
  reflexivity.
Qed.

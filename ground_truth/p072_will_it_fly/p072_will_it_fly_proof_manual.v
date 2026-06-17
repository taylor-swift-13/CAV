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
From SimpleC.EE.CAV.ground_truth_p072_will_it_fly Require Import p072_will_it_fly_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p072_will_it_fly.
Local Open Scope sac.

Lemma proof_of_p072_will_it_fly_safety_wit_7 : p072_will_it_fly_safety_wit_7.
Proof.
  pre_process.
  subst s.
  rewrite sum_sublist_snoc by lia.
  entailer!;
  match goal with
  | H: will_it_fly_int_range _ |- _ =>
      unfold will_it_fly_int_range in H;
      specialize (H (i + 1)); lia
  end.
Qed.

Lemma proof_of_p072_will_it_fly_entail_wit_1 : p072_will_it_fly_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_p072_will_it_fly_entail_wit_2 : p072_will_it_fly_entail_wit_2.
Proof.
  pre_process.
  subst s.
  rewrite sum_sublist_snoc by lia.
  entailer!.
  apply mirror_prefix_extend with (n := q_size_pre); auto; lia.
Qed.

Lemma proof_of_p072_will_it_fly_return_wit_1 : p072_will_it_fly_return_wit_1.
Proof.
  pre_process.
  assert (Hsfull: s = sum lv).
  {
    match goal with
    | Hs: s = sum (sublist 0 i lv) |- _ => rewrite Hs
    end.
    replace i with (Zlength lv) by lia.
    rewrite sublist_self by reflexivity.
    reflexivity.
  }
  entailer!.
  apply problem_72_spec_true.
  - apply mirror_prefix_full with (n := q_size_pre) (i := i); auto; lia.
  - lia.
Qed.

Lemma proof_of_p072_will_it_fly_return_wit_2 : p072_will_it_fly_return_wit_2.
Proof.
  pre_process.
  assert (Hsum_gt: sum lv > w_pre).
  {
    rewrite H8 in H.
    replace i with (Zlength lv) in H by lia.
    rewrite sublist_self in H by reflexivity.
    exact H.
  }
  entailer!.
  apply problem_72_spec_weight_false.
  - apply mirror_prefix_full with (n := q_size_pre) (i := i); auto; lia.
  - lia.
Qed.

Lemma proof_of_p072_will_it_fly_return_wit_3 : p072_will_it_fly_return_wit_3.
Proof.
  pre_process.
  entailer!.
  apply mirror_prefix_mismatch_spec_false with (n := q_size_pre) (i := i); auto; lia.
Qed.

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
From SimpleC.EE.CAV.verify_20260608_123342_p138_is_equal_to_sum_even Require Import p138_is_equal_to_sum_even_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p138_is_equal_to_sum_even.
Local Open Scope sac.

Lemma proof_of_p138_is_equal_to_sum_even_return_wit_1 : p138_is_equal_to_sum_even_return_wit_1.
Proof.
  intros n_pre.
  repeat (split_pure_spatial || split_pures).
  - Intros_p Hodd.
    Intros_p Hmin.
    Intros_p Hmax.
    cancel.
  - Intros_p Hodd.
    Intros_p Hmin.
    Intros_p Hmax.
    dump_pre_spatial.
    unfold problem_138_spec.
    split.
    + intros Hnz.
      exfalso; apply Hnz; reflexivity.
    + intros [_ Heven].
      exfalso.
      pose proof (Z.rem_mod_eq_0 n_pre 2 ltac:(lia)) as Hrem_mod.
      apply Hodd.
      apply (proj2 Hrem_mod).
      exact Heven.
Qed.

Lemma proof_of_p138_is_equal_to_sum_even_return_wit_2 : p138_is_equal_to_sum_even_return_wit_2.
Proof.
  intros n_pre.
  repeat (split_pure_spatial || split_pures).
  - Intros_p Hlt8.
    Intros_p Heven.
    Intros_p Hmin.
    Intros_p Hmax.
    cancel.
  - Intros_p Hlt8.
    Intros_p Heven.
    Intros_p Hmin.
    Intros_p Hmax.
    dump_pre_spatial.
    unfold problem_138_spec.
    split.
    + intros Hnz.
      exfalso.
      apply Hnz.
      reflexivity.
    + intros [Hge8 _].
      lia.
Qed.

Lemma proof_of_p138_is_equal_to_sum_even_return_wit_3 : p138_is_equal_to_sum_even_return_wit_3.
Proof.
  intros n_pre.
  repeat (split_pure_spatial || split_pures).
  - Intros_p Hge8.
    Intros_p Heven.
    Intros_p Hmin.
    Intros_p Hmax.
    cancel.
  - Intros_p Hge8.
    Intros_p Heven.
    Intros_p Hmin.
    Intros_p Hmax.
    dump_pre_spatial.
    unfold problem_138_spec.
    split.
    + intros _.
      pose proof (Z.rem_mod_eq_0 n_pre 2 ltac:(lia)) as Hrem_mod.
      split.
      * lia.
      * apply (proj1 Hrem_mod).
        exact Heven.
    + intros _.
      discriminate.
Qed.

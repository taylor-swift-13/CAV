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
From SimpleC.EE.CAV.verify_20260606_155626_p138_is_equal_to_sum_even Require Import p138_is_equal_to_sum_even_goal.
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
  pre_process.
  entailer!.
  split.
  - intros Hz. exfalso. apply Hz. reflexivity.
  - intros (e1 & e2 & e3 & e4 & He1 & He2 & He3 & He4 & Hsum) Hz.
    destruct He1 as [k1 [He1 Hk1]].
    destruct He2 as [k2 [He2 Hk2]].
    destruct He3 as [k3 [He3 Hk3]].
    destruct He4 as [k4 [He4 Hk4]].
    assert (Hdiv : (2 | n_pre)).
    { exists (k1 + k2 + k3 + k4). lia. }
    pose proof (proj2 (Z.rem_divide n_pre 2 ltac:(lia)) Hdiv) as Hrem.
    apply H in Hrem. contradiction.
Qed.

Lemma proof_of_p138_is_equal_to_sum_even_return_wit_2 : p138_is_equal_to_sum_even_return_wit_2.
Proof.
  pre_process.
  entailer!.
  split.
  - intros Hz. exfalso. apply Hz. reflexivity.
  - intros (e1 & e2 & e3 & e4 & He1 & He2 & He3 & He4 & Hsum) Hz.
    destruct He1 as [k1 [He1 Hk1]].
    destruct He2 as [k2 [He2 Hk2]].
    destruct He3 as [k3 [He3 Hk3]].
    destruct He4 as [k4 [He4 Hk4]].
    lia.
Qed.

Lemma proof_of_p138_is_equal_to_sum_even_return_wit_3 : p138_is_equal_to_sum_even_return_wit_3.
Proof.
  pre_process.
  entailer!.
  split.
  - intros _.
    pose proof (proj1 (Z.rem_divide n_pre 2 ltac:(lia)) H0) as Hdiv.
    destruct Hdiv as [t Ht].
    exists 2, 2, 2, (2 * (t - 3)).
    repeat split.
    + exists 1. lia.
    + exists 1. lia.
    + exists 1. lia.
    + exists (t - 3). split; lia.
    + lia.
  - intros _ Hz. lia.
Qed.

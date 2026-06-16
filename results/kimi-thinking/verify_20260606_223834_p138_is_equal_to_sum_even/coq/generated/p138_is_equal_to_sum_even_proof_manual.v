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
From SimpleC.EE.CAV.verify_20260606_223834_p138_is_equal_to_sum_even Require Import p138_is_equal_to_sum_even_goal.
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
  unfold problem_138_spec.
  split.
  - intro Hf. exfalso. apply Hf. reflexivity.
  - intro Hexists.
    destruct Hexists as [e1 [e2 [e3 [e4 [Hev1 [Hev2 [Hev3 [Hev4 Heq]]]]]]]].
    unfold is_positive_even in Hev1, Hev2, Hev3, Hev4.
    destruct Hev1 as [k1 [Hek1 Hkk1]].
    destruct Hev2 as [k2 [Hek2 Hkk2]].
    destruct Hev3 as [k3 [Hek3 Hkk3]].
    destruct Hev4 as [k4 [Hek4 Hkk4]].
    assert (n_pre = 2 * (k1 + k2 + k3 + k4)) by lia.
    assert (n_pre % 2 = 0) as Hmod.
    { rewrite H2. replace (2 * (k1 + k2 + k3 + k4)) with ((k1 + k2 + k3 + k4) * 2) by lia. apply Z.rem_mul. lia. }
    exfalso. exact (H Hmod).
Qed.

Lemma proof_of_p138_is_equal_to_sum_even_return_wit_2 : p138_is_equal_to_sum_even_return_wit_2.
Proof.
  pre_process.
  entailer!.
  unfold problem_138_spec.
  split.
  - intro Hf. exfalso. apply Hf. reflexivity.
  - intro Hexists.
    destruct Hexists as [e1 [e2 [e3 [e4 [Hev1 [Hev2 [Hev3 [Hev4 Heq]]]]]]]].
    unfold is_positive_even in Hev1, Hev2, Hev3, Hev4.
    destruct Hev1 as [k1 [Hek1 Hkk1]].
    destruct Hev2 as [k2 [Hek2 Hkk2]].
    destruct Hev3 as [k3 [Hek3 Hkk3]].
    destruct Hev4 as [k4 [Hek4 Hkk4]].
    assert (e1 >= 2) by lia.
    assert (e2 >= 2) by lia.
    assert (e3 >= 2) by lia.
    assert (e4 >= 2) by lia.
    lia.
Qed.

Lemma proof_of_p138_is_equal_to_sum_even_return_wit_3 : p138_is_equal_to_sum_even_return_wit_3.
Proof.
  pre_process.
  entailer!.
  unfold problem_138_spec.
  split.
  - intro.
    exists 2, 2, 2, (n_pre - 6).
    repeat split;
    try solve [unfold is_positive_even; exists 1; lia];
    try solve [assert (n_pre = 2 * (Z.quot n_pre 2)) as Heq2 by
               (pose proof (Z.quot_exact n_pre 2 ltac:(lia)) as Hq;
                destruct Hq as [Hq1 Hq2]; apply Hq2; exact H0);
               unfold is_positive_even; exists (Z.quot n_pre 2 - 3);
               split; [lia | lia]];
    try solve [assert (n_pre = 2 * (Z.quot n_pre 2)) as Heq2 by
               (pose proof (Z.quot_exact n_pre 2 ltac:(lia)) as Hq;
                destruct Hq as [Hq1 Hq2]; apply Hq2; exact H0);
               nia].
  - intro. easy.
Qed.

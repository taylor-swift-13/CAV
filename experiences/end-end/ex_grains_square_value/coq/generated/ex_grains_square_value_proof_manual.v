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
From SimpleC.EE.CAV.verify_20260605_080500v_ex_grains_square_value Require Import ex_grains_square_value_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import power_nonnegative.
Local Open Scope sac.

Lemma power_nonnegative_z_step :
  forall i : Z,
    1 <= i ->
    power_nonnegative_z 2 i = power_nonnegative_z 2 (i - 1) * 2.
Proof.
  intros i Hi.
  unfold power_nonnegative_z.
  replace i with ((i - 1) + 1) by lia.
  rewrite Z2Nat.inj_add by lia.
  simpl.
  rewrite Nat.add_1_r.
  replace (i - 1 + 1 - 1) with (i - 1) by lia.
  reflexivity.
Qed.

Lemma proof_of_ex_grains_square_value_safety_wit_3 : ex_grains_square_value_safety_wit_3.
Proof.
  pre_process.
  entailer!.
  - rewrite H2.
    rewrite <- power_nonnegative_z_step by lia.
    pose proof (H4 i) as Hi_range.
    assert (0 <= i <= square_pre - 1) by lia.
    specialize (Hi_range H5).
    lia.
  - rewrite H2.
    rewrite <- power_nonnegative_z_step by lia.
    pose proof (H4 i) as Hi_range.
    assert (0 <= i <= square_pre - 1) by lia.
    specialize (Hi_range H5).
    lia.
Qed.

Lemma proof_of_ex_grains_square_value_entail_wit_1 : ex_grains_square_value_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_ex_grains_square_value_entail_wit_2 : ex_grains_square_value_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  rewrite H2.
  rewrite <- power_nonnegative_z_step by lia.
  replace (i + 1 - 1) with i by lia.
  reflexivity.
Qed.

Lemma proof_of_ex_grains_square_value_return_wit_1 : ex_grains_square_value_return_wit_1.
Proof.
  pre_process.
  entailer!.
  assert (i = square_pre) by lia.
  subst i.
  exact H2.
Qed.

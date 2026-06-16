Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260606_224831_p085_add Require Import p085_add_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p085_add.
Local Open Scope sac.

Lemma proof_of_p085_add_safety_wit_14 : p085_add_safety_wit_14.
Proof.
  pre_process.
  match goal with
  | Hrange : add_int_range ?lv,
    Hlen : lst_size_pre = Zlength lv |- _ =>
      assert (Hidx : 2 * i + 1 < Zlength lv) by (rewrite <- Hlen; lia);
      specialize (Hrange i ltac:(lia) Hidx);
      destruct Hrange as [_ Hrange];
      destruct Hrange as [Hlo Hhi]
  end.
  split_pures.
  - dump_pre_spatial.
    subst s.
    replace (i * 2 + 1) with (2 * i + 1) by lia.
    exact Hhi.
  - dump_pre_spatial.
    subst s.
    replace (i * 2 + 1) with (2 * i + 1) by lia.
    exact Hlo.
Qed.

Lemma proof_of_p085_add_entail_wit_1 : p085_add_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_p085_add_entail_wit_2_1 : p085_add_entail_wit_2_1.
Proof.
  pre_process.
  split_pures.
  split_pure_spatial.
  - cancel (IntArray.full lst_pre lst_size_pre lv).
  - split_pures.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + unfold sum_even_at_odd_upto.
      dump_pre_spatial.
      subst s.
      replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      simpl.
      replace
        (match Z.of_nat (Z.to_nat i) with
         | 0 => 0
         | Z.pos y' => Z.pos y'~0
         | Z.neg y' => Z.neg y'~0
         end + 1)
        with (i * 2 + 1) by (rewrite Z2Nat.id by lia; destruct i; lia).
      assert (Heven : (Znth (i * 2 + 1) lv 0 % 2 =? 0) = true).
      { apply Z.eqb_eq. exact H. }
      rewrite Heven.
      unfold sum_even_at_odd_upto at 1.
      reflexivity.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; exact H6.
    + dump_pre_spatial; exact H7.
    + dump_pre_spatial; exact H8.
Qed.

Lemma proof_of_p085_add_entail_wit_2_2 : p085_add_entail_wit_2_2.
Proof.
  pre_process.
  split_pures.
  split_pure_spatial.
  - cancel (IntArray.full lst_pre lst_size_pre lv).
  - split_pures.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + unfold sum_even_at_odd_upto.
      dump_pre_spatial.
      subst s.
      replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      simpl.
      replace
        (match Z.of_nat (Z.to_nat i) with
         | 0 => 0
         | Z.pos y' => Z.pos y'~0
         | Z.neg y' => Z.neg y'~0
         end + 1)
        with (i * 2 + 1) by (rewrite Z2Nat.id by lia; destruct i; lia).
      assert (Hodd : (Znth (i * 2 + 1) lv 0 % 2 =? 0) = false).
      { apply Z.eqb_neq. exact H. }
      rewrite Hodd.
      unfold sum_even_at_odd_upto at 1.
      reflexivity.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; exact H6.
    + dump_pre_spatial; exact H7.
    + dump_pre_spatial; exact H8.
Qed.

Lemma proof_of_p085_add_return_wit_1 : p085_add_return_wit_1.
Proof.
  pre_process.
  split_pures.
  split_pure_spatial.
  - cancel (IntArray.full lst_pre lst_size_pre lv).
  - dump_pre_spatial.
    unfold problem_85_spec.
    subst s.
    rewrite <- H5.
    f_equal.
    apply Z.div_unique with (r := lst_size_pre - 2 * i).
    + left; lia.
    + lia.
Qed.

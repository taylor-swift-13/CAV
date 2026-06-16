Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From SimpleC.EE.CAV.verify_20260608_125304_p121_solutions Require Import p121_solutions_goal.
Import naive_C_Rules.
Require Import p121_solutions.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Local Open Scope sac.

Lemma proof_of_p121_solutions_safety_wit_3 : p121_solutions_safety_wit_3.
Proof.
  pre_process.
  entailer!.
  lia.
Qed.

Lemma proof_of_p121_solutions_safety_wit_10 : p121_solutions_safety_wit_10.
Proof.
  pre_process.
  match goal with
  | Hrange: sum_odd_at_even_int_range lv |- _ =>
      pose proof (Hrange i ltac:(lia) ltac:(lia)) as [? ?]
  end.
  entailer!.
  lia.
Qed.

Lemma proof_of_p121_solutions_entail_wit_1 : p121_solutions_entail_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  cancel.
  split_pures; auto.
  unfold sum_odd_at_even_upto.
  reflexivity.
Qed.

Lemma proof_of_p121_solutions_entail_wit_2_1 : p121_solutions_entail_wit_2_1.
Proof.
  pre_process.
  split_pure_spatial.
  cancel.
  split_pures; auto.
  unfold sum_odd_at_even_upto in *.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  rewrite Z2Nat.id by lia.
  rewrite H2.
  rewrite H.
  reflexivity.
Qed.

Lemma proof_of_p121_solutions_entail_wit_2_2 : p121_solutions_entail_wit_2_2.
Proof.
  pre_process.
  split_pure_spatial.
  cancel.
  split_pures; auto.
  unfold sum_odd_at_even_upto in *.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  rewrite Z2Nat.id by lia.
  rewrite H1.
  destruct (Z.eqb (Znth (i * 2) lv 0 mod 2) 1) eqn:Heq.
  - apply Z.eqb_eq in Heq. lia.
  - reflexivity.
Qed.

Lemma proof_of_p121_solutions_return_wit_1 : p121_solutions_return_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  cancel.
  split_pures; auto.
  unfold problem_121_spec.
  rewrite H2.
  unfold sum_odd_at_even_upto.
  assert (Hlen : lst_size = Zlength lv) by lia.
  rewrite Hlen in H.
  rewrite Hlen in H0.
  assert (Hstop: forall n,
      (Z.to_nat i <= n)%nat ->
      (n <= Z.to_nat (Zlength lv))%nat ->
      sum_odd_at_even_upto_nat n lv = sum_odd_at_even_upto_nat (Z.to_nat i) lv).
  {
    intros n Hni Hnlen.
    induction n as [|n IH].
    - lia.
    - destruct (Nat.eq_dec (S n) (Z.to_nat i)).
      + subst. reflexivity.
      + assert (Hprev: (Z.to_nat i <= n)%nat) by lia.
        rewrite <- IH by lia.
        simpl.
        assert (2 * Z.of_nat n >= Zlength lv) by lia.
        assert (Znth (2 * Z.of_nat n) lv 0 = 0).
        {
          unfold Znth.
          destruct (Z_lt_dec (2 * Z.of_nat n) 0); [lia|].
          rewrite nth_overflow by (rewrite Zlength_correct; lia).
          reflexivity.
        }
        rewrite H4.
        rewrite Z.rem_0_l by lia.
        reflexivity.
  }
  symmetry.
  apply Hstop; lia.
Qed.

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
From SimpleC.EE.CAV.verify_20260608_175604_p100_make_a_pile Require Import p100_make_a_pile_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p100_make_a_pile.
Local Open Scope sac.

Lemma proof_of_p100_make_a_pile_safety_wit_2 : p100_make_a_pile_safety_wit_2.
Proof.
  pre_process.
  entailer!.
  lazymatch goal with
  | Hrange: pile_int_range ?n |- _ =>
      unfold pile_int_range in Hrange;
      pose proof (Hrange i ltac:(lia)) as Hr;
      lia
  end.
Qed.

Lemma proof_of_p100_make_a_pile_safety_wit_3 : p100_make_a_pile_safety_wit_3.
Proof.
  pre_process.
  entailer!.
  lazymatch goal with
  | Hrange: pile_int_range ?n |- _ =>
      unfold pile_int_range in Hrange;
      pose proof (Hrange i ltac:(lia)) as Hr;
      lia
  end.
Qed.

Lemma proof_of_p100_make_a_pile_entail_wit_1 : p100_make_a_pile_entail_wit_1.
Proof.
  pre_process.
  rewrite H1.
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval_2 n0).
  rewrite Zsublist_nil by lia.
  setoid_rewrite (IntArray.full_empty retval_2 0).
  entailer!.
Qed.

Lemma proof_of_p100_make_a_pile_entail_wit_3 : p100_make_a_pile_entail_wit_3.
Proof.
  pre_process.
  entailer!.
  assert (Zlength (make_pile n0) = n0) as Hlen.
  {
    unfold make_pile.
    rewrite Zlength_correct.
    rewrite map_length, Zseq_length.
    lia.
  }
  assert (sublist 0 (i + 1) (make_pile n0) =
          sublist 0 i (make_pile n0) ++ (n0 + 2 * i) :: nil) as Hsub.
  {
    assert (Znth i (make_pile n0) 0 = n0 + 2 * i) as Hnth.
    {
      unfold make_pile, Znth.
      remember (fun i0 : Z => n0 + 2 * i0) as f.
      rewrite nth_indep with (d' := f 0).
      2: rewrite map_length, Zseq_length; lia.
      rewrite map_nth.
      subst f.
      replace (nth (Z.to_nat i) (Zseq 0 (Z.to_nat n0)) 0) with i.
      2: { rewrite Zseq_nth; lia. }
      lia.
    }
    rewrite sublist_split with (mid := i).
    2: lia.
    2: rewrite Hlen; lia.
    rewrite (sublist_single 0 i (make_pile n0)).
    2: rewrite Hlen; lia.
    rewrite Hnth.
    reflexivity.
  }
  rewrite Hsub.
  cancel (IntArray.full data_2 (i + 1)
            (sublist 0 i (make_pile n0) ++ (n0 + 2 * i) :: nil)).
Qed.

Lemma proof_of_p100_make_a_pile_return_wit_1 : p100_make_a_pile_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = n0) by lia.
  assert (Zlength (make_pile n0) = n0) as Hlen.
  {
    unfold make_pile.
    rewrite Zlength_correct.
    rewrite map_length, Zseq_length.
    lia.
  }
  Exists (make_pile n0).
  Exists n0.
  Exists data_3.
  entailer!.
  - subst i.
    rewrite sublist_self by (symmetry; exact Hlen).
    setoid_rewrite (IntArray.undef_seg_empty data_3 n0).
    cancel (IntArray.full data_3 n0 (make_pile n0)).
    cancel emp.
  - unfold problem_100_spec.
    split; [lia|].
    split; [exact Hlen|].
    intros j Hj.
    unfold make_pile, Znth.
    remember (fun i0 : Z => n0 + 2 * i0) as f.
    rewrite nth_indep with (d' := f 0).
    2: rewrite map_length, Zseq_length; lia.
    rewrite map_nth.
    subst f.
    replace (nth (Z.to_nat j) (Zseq 0 (Z.to_nat n0)) 0) with j.
    2: { rewrite Zseq_nth; lia. }
    lia.
Qed.

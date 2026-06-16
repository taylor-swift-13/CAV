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
Require Import p100_make_a_pile_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p100_make_a_pile.
Local Open Scope sac.

Lemma proof_of_p100_make_a_pile_entail_wit_1 : p100_make_a_pile_entail_wit_1.
Proof.
  pre_process.
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval_2 n_pre).
  Exists retval_2.
  change (sublist 0 0 (make_pile n0)) with (@nil Z).
  rewrite (IntArray.seg_empty retval_2 0 0).
  subst n_pre.
  entailer!.
Qed.

Lemma proof_of_p100_make_a_pile_entail_wit_3 : p100_make_a_pile_entail_wit_3.
Proof.
  pre_process.
  assert (Hlen : Zlength (make_pile n0) = n0).
  {
    unfold make_pile.
    rewrite Zlength_correct.
    rewrite map_length, Zseq_length, Z2Nat.id by lia.
    lia.
  }
  sep_apply (IntArray.seg_single data i (n0 + 2 * i)).
  sep_apply (IntArray.seg_merge_to_seg data 0 i (i + 1)
    (sublist 0 i (make_pile n0)) ((n0 + 2 * i) :: nil)).
  2: { lia. }
  replace (sublist 0 (i + 1) (make_pile n0))
    with (sublist 0 i (make_pile n0) ++ (n0 + 2 * i) :: nil).
  2: {
    rewrite (sublist_split 0 (i + 1) i (make_pile n0)) by lia.
    rewrite (sublist_single 0 i (make_pile n0)) by lia.
    unfold Znth, make_pile.
    rewrite nth_indep with (d' := (fun i0 : Z => n0 + 2 * i0) 0).
    2: {
      rewrite map_length, Zseq_length.
      apply Z2Nat.inj_lt; lia.
    }
    rewrite map_nth.
    rewrite Zseq_nth by lia.
    reflexivity.
  }
  Exists data.
  split_pure_spatial.
  - cancel (IntArray.seg data 0 (i + 1) (sublist 0 i (make_pile n0) ++ (n0 + 2 * i) :: nil)).
    cancel ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data).
    cancel ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0).
    cancel (IntArray.undef_seg data (i + 1) n0).
  - split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_p100_make_a_pile_return_wit_1 : p100_make_a_pile_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = n0) by lia.
  subst i.
  assert (Hlen : Zlength (make_pile n0) = n0).
  {
    unfold make_pile.
    rewrite Zlength_correct.
    rewrite map_length, Zseq_length, Z2Nat.id by lia.
    lia.
  }
  rewrite IntArray.undef_seg_empty.
  sep_apply (IntArray.seg_to_full data_2 0 n0 (make_pile n0)).
  replace (data_2 + 0 * sizeof (INT)) with data_2 by lia.
  rewrite Z.sub_0_r.
  Exists (make_pile n0), n0, data_2.
  split_pure_spatial.
  - cancel (IntArray.full data_2 n0 (make_pile n0)).
    cancel ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2).
    cancel ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n0).
  - split_pures.
    + dump_pre_spatial. exact H0.
    + dump_pre_spatial. exact Hlen.
    + dump_pre_spatial. reflexivity.
    + unfold problem_100_spec.
      split; [lia | split].
      * exact Hlen.
      * intros j Hj.
        unfold make_pile, Znth.
        rewrite nth_indep with (d' := (fun i0 : Z => n0 + 2 * i0) 0).
        2: {
          rewrite map_length, Zseq_length.
          apply Z2Nat.inj_lt; lia.
        }
        rewrite map_nth.
        rewrite Zseq_nth by lia.
        lia.
Qed.

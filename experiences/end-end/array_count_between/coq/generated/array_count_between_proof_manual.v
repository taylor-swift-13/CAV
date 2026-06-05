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
From SimpleC.EE.CAV.verify_20260604_230601v_array_count_between Require Import array_count_between_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_count_between.

Lemma array_count_between_spec_bounds :
  forall l lo hi,
    0 <= array_count_between_spec l lo hi <= Zlength l.
Proof.
  induction l.
  - intros. simpl. rewrite Zlength_nil. split; lia.
  - intros. simpl. destruct (Z_le_dec lo a); destruct (Z_le_dec a hi); simpl in *.
    + specialize (IHl lo hi) as [IHlo IHhi]. rewrite Zlength_cons. split.
      * remember (array_count_between_spec l lo hi) as c eqn:Hc.
        destruct c.
        -- simpl. lia.
        -- destruct p; simpl; lia.
        -- exfalso. lia.
      * remember (array_count_between_spec l lo hi) as c eqn:Hc.
        destruct c.
        -- simpl. lia.
        -- destruct p; simpl; lia.
        -- exfalso. lia.
    + specialize (IHl lo hi) as [IHlo IHhi]. rewrite Zlength_cons. split.
      * exact IHlo.
      * lia.
    + specialize (IHl lo hi) as [IHlo IHhi]. rewrite Zlength_cons. split.
      * exact IHlo.
      * lia.
    + specialize (IHl lo hi) as [IHlo IHhi]. rewrite Zlength_cons. split.
      * exact IHlo.
      * lia.
Qed.

Lemma array_count_between_spec_app_single :
  forall l x lo hi,
    array_count_between_spec (l ++ cons x nil) lo hi =
    array_count_between_spec l lo hi +
    (if Z_le_dec lo x then
       if Z_le_dec x hi then 1 else 0
     else 0).
Proof.
  induction l.
  - intros. simpl. lia.
  - intros. simpl. rewrite IHl.
    remember (array_count_between_spec l lo hi) as c eqn:Hc.
    pose proof (array_count_between_spec_bounds l lo hi) as [Hc_nonneg _].
    rewrite <- Hc in Hc_nonneg.
    destruct (Z_le_dec lo a); destruct (Z_le_dec a hi);
    destruct (Z_le_dec lo x); destruct (Z_le_dec x hi);
    destruct c; simpl in *; try lia.
    all: try (destruct p; simpl; lia).
Qed.

Lemma sublist_prefix_succ :
  forall l i,
    0 <= i < Zlength l ->
    sublist 0 (i + 1) l = sublist 0 i l ++ cons (Znth i l 0) nil.
Proof.
  intros.
  rewrite (sublist_split 0 (i + 1) i l).
  - rewrite (sublist_single 0 i l) by lia. reflexivity.
  - lia.
  - lia.
Qed.

Local Open Scope sac.

Lemma proof_of_array_count_between_safety_wit_3 : array_count_between_safety_wit_3.
Proof.
  pre_process; entailer!.
  - match goal with
    | Hspec: count = array_count_between_spec (sublist 0 i l) lo_pre hi_pre |- _ =>
        rewrite Hspec
      end.
    pose proof (array_count_between_spec_bounds (sublist 0 i l) lo_pre hi_pre) as [Hb_lo _].
    lia.
  - match goal with
    | Hspec: count = array_count_between_spec (sublist 0 i l) lo_pre hi_pre |- _ =>
        rewrite Hspec
      end.
    pose proof (array_count_between_spec_bounds (sublist 0 i l) lo_pre hi_pre) as [Hb_lo Hb_hi].
    match goal with
    | Hlen: Zlength l = n_pre |- _ =>
        rewrite Zlength_sublist0 in Hb_hi by (rewrite Hlen; lia)
      end.
    assert (i <= INT_MAX) by lia.
    lia.
Qed.

Lemma proof_of_array_count_between_entail_wit_2 : array_count_between_entail_wit_2.
Proof.
  pre_process.
Qed.

Lemma proof_of_array_count_between_entail_wit_3_1 : array_count_between_entail_wit_3_1.
Proof.
  pre_process; entailer!.
  rewrite sublist_prefix_succ by
    match goal with
    | Hlen: Zlength l = n_pre |- _ => rewrite Hlen; lia
    end.
  rewrite array_count_between_spec_app_single.
  match goal with
  | Hspec: count = array_count_between_spec (sublist 0 i l) lo_pre hi_pre |- _ =>
      rewrite Hspec
  end.
  destruct (Z_le_dec lo_pre (Znth i l 0)).
  - destruct (Z_le_dec (Znth i l 0) hi_pre).
    + lia.
    + lia.
  - lia.
Qed.

Lemma proof_of_array_count_between_entail_wit_3_2 : array_count_between_entail_wit_3_2.
Proof.
  pre_process; entailer!.
  rewrite sublist_prefix_succ by
    match goal with
    | Hlen: Zlength l = n_pre |- _ => rewrite Hlen; lia
    end.
  rewrite array_count_between_spec_app_single.
  match goal with
  | Hspec: count = array_count_between_spec (sublist 0 i l) lo_pre hi_pre |- _ =>
      rewrite Hspec
  end.
  destruct (Z_le_dec lo_pre (Znth i l 0)).
  - lia.
  - lia.
Qed.

Lemma proof_of_array_count_between_entail_wit_3_3 : array_count_between_entail_wit_3_3.
Proof.
  pre_process; entailer!.
  rewrite sublist_prefix_succ by
    match goal with
    | Hlen: Zlength l = n_pre |- _ => rewrite Hlen; lia
    end.
  rewrite array_count_between_spec_app_single.
  match goal with
  | Hspec: count = array_count_between_spec (sublist 0 i l) lo_pre hi_pre |- _ =>
      rewrite Hspec
  end.
  destruct (Z_le_dec lo_pre (Znth i l 0)).
  - destruct (Z_le_dec (Znth i l 0) hi_pre).
    + lia.
    + lia.
  - lia.
Qed.

Lemma proof_of_array_count_between_return_wit_1 : array_count_between_return_wit_1.
Proof.
  pre_process; entailer!.
  assert (i = n_pre) by lia.
  subst i.
  rewrite H2.
  rewrite sublist_self by exact (eq_sym H13).
  reflexivity.
Qed.

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
From SimpleC.EE.CAV.ground_truth_p140_fix_spaces Require Import p140_fix_spaces_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
From AUXLib Require Import ListLib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p140_fix_spaces.
Local Open Scope sac.

Ltac solve_fix_pending :=
  match goal with
  | H : fix_spaces_pending ?i ?l = ?p |- fix_spaces_pending ?i ?l = ?p =>
      exact H
  | H : ?p = fix_spaces_pending ?i ?l |- fix_spaces_pending ?i ?l = ?p =>
      symmetry; exact H
  | Hstate : ?sp = fix_spaces_pending ?i ?l,
    Hval : ?sp = ?p |- fix_spaces_pending ?i ?l = ?p =>
      rewrite <- Hstate; exact Hval
  | Hstate : ?sp = fix_spaces_pending ?i ?l,
    Hval : ?p = ?sp |- fix_spaces_pending ?i ?l = ?p =>
      rewrite <- Hstate; symmetry; exact Hval
  | Hstate : fix_spaces_pending ?i ?l = ?sp,
    Hval : ?sp = ?p |- fix_spaces_pending ?i ?l = ?p =>
      rewrite Hstate; exact Hval
  | Hstate : fix_spaces_pending ?i ?l = ?sp,
    Hval : ?p = ?sp |- fix_spaces_pending ?i ?l = ?p =>
      rewrite Hstate; symmetry; exact Hval
  end.

Ltac derive_out_nonzero :=
  unfold list_nonzero; intros ? ?;
  match goal with
  | H : forall j : Z, 0 <= j /\ j < Zlength ?out -> Znth j ?out 0 <> 0 |- _ =>
      apply H; lia
  | Hlen : ?k = Zlength ?out,
    H : forall j : Z, 0 <= j /\ j < ?k -> Znth j ?out 0 <> 0 |- _ =>
      apply H; lia
  | Hlen : Zlength ?out = ?k,
    H : forall j : Z, 0 <= j /\ j < ?k -> Znth j ?out 0 <> 0 |- _ =>
      apply H; lia
  end.

Ltac solve_ascii_range_char :=
  try solve [lia];
  match goal with
  | Hrange : ascii_range ?l |- context[Znth ?idx ?l 0] =>
      pose proof (Hrange idx ltac:(lia)); lia
  | Hrange : forall j : Z, 0 <= j < Zlength ?l -> 0 <= Znth j ?l 0 <= 127
    |- context[Znth ?idx ?l 0] =>
      pose proof (Hrange idx ltac:(lia)); lia
  | Hlen : Zlength ?l = ?len,
    Hrange : forall j : Z, 0 <= j < ?len -> 0 <= Znth j ?l 0 <= 127
    |- context[Znth ?idx ?l 0] =>
      pose proof (Hrange idx ltac:(lia)); lia
  | Hlen : ?len = Zlength ?l,
    Hrange : forall j : Z, 0 <= j < ?len -> 0 <= Znth j ?l 0 <= 127
    |- context[Znth ?idx ?l 0] =>
      pose proof (Hrange idx ltac:(lia)); lia
  end.

Ltac solve_input_char_nonzero :=
  match goal with
  | |- Znth ?i ?l 0 <> 0 =>
      match goal with
      | H : forall j : Z, 0 <= j /\ j < Zlength l -> Znth j l 0 <> 0 |- _ =>
          apply H; lia
      | Hlen : Zlength l = ?len,
        H : forall j : Z, 0 <= j /\ j < ?len -> Znth j l 0 <> 0 |- _ =>
          apply H; lia
      | Hlen : ?len = Zlength l,
        H : forall j : Z, 0 <= j /\ j < ?len -> Znth j l 0 <> 0 |- _ =>
          apply H; lia
      end
  | |- ?x <> 0 => lia
  end.

Ltac solve_list_nonzero_fact :=
  repeat apply list_nonzero_app;
  try derive_out_nonzero;
  try (apply list_nonzero_single; solve_input_char_nonzero);
  try (apply list_nonzero_single; lia).

Ltac solve_list_nonzero_goal :=
  match goal with
  | |- list_nonzero _ =>
      solve_list_nonzero_fact
  | |- forall j : Z, 0 <= j < ?bound -> Znth j ?out 0 <> 0 =>
      let Hnz := fresh "Hnz" in
      assert (Hnz : list_nonzero out) by solve_list_nonzero_fact;
      unfold list_nonzero in Hnz;
      intros j Hj; apply Hnz;
      rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia
  | |- forall j : Z, 0 <= j /\ j < ?bound -> Znth j ?out 0 <> 0 =>
      let Hnz := fresh "Hnz" in
      assert (Hnz : list_nonzero out) by solve_list_nonzero_fact;
      unfold list_nonzero in Hnz;
      intros j Hj; apply Hnz;
      rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia
  end.

Lemma proof_of_p140_fix_spaces_entail_wit_1 : p140_fix_spaces_entail_wit_1.
Proof.
  unfold p140_fix_spaces_entail_wit_1.
  intros.
  pre_process.
  subst retval_2.
  Exists (@nil Z).
  destruct (fix_spaces_state_0 l) as [Hp Hpend].
  sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 (len + 1)).
  rewrite (CharArray.undef_seg_empty retval 0).
  rewrite (CharArray.full_empty retval 0).
  entailer!.
  - lia.
Qed.

Lemma proof_of_p140_fix_spaces_entail_wit_2_1 : p140_fix_spaces_entail_wit_2_1.
Proof.
  unfold p140_fix_spaces_entail_wit_2_1.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  Exists out_l_2.
  entailer!.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_space i l ltac:(lia) ltac:(assumption)) as [_ Hpend].
    symmetry; exact Hpend.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_space i l ltac:(lia) ltac:(assumption)) as [Hp _].
    symmetry; exact Hp.
Qed.

Lemma proof_of_p140_fix_spaces_entail_wit_2_2 : p140_fix_spaces_entail_wit_2_2.
Proof.
  unfold p140_fix_spaces_entail_wit_2_2.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  assert (Hsp0 : spacelen = 0) by lia.
  rewrite (signed_last_nbits_eq (Znth i l 0) 8) by solve_ascii_range_char.
  Exists (out_l_2 ++ cons (Znth i l 0) nil).
  entailer!.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_nonspace_pending0 i l ltac:(lia) ltac:(assumption) ltac:(exact Hsp0))
      as [_ Hpend].
    symmetry; exact Hpend.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_nonspace_pending0 i l ltac:(lia) ltac:(assumption) ltac:(exact Hsp0))
      as [Hp _].
    symmetry; exact Hp.
  - solve_list_nonzero_goal.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_p140_fix_spaces_entail_wit_2_3 : p140_fix_spaces_entail_wit_2_3.
Proof.
  unfold p140_fix_spaces_entail_wit_2_3.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  rewrite (signed_last_nbits_eq (Znth i l 0) 8) by solve_ascii_range_char.
  Exists ((out_l_2 ++ cons 45 nil) ++ cons (Znth i l 0) nil).
  entailer!.
  - subst out_l_2.
    destruct (fix_spaces_step_nonspace_pending_more i l spacelen ltac:(lia) ltac:(assumption) ltac:(assumption) ltac:(lia))
      as [_ Hpend].
    symmetry; exact Hpend.
  - subst out_l_2.
    destruct (fix_spaces_step_nonspace_pending_more i l spacelen ltac:(lia) ltac:(assumption) ltac:(assumption) ltac:(lia))
      as [Hp _].
    symmetry; exact Hp.
  - solve_list_nonzero_goal.
  - rewrite !Zlength_app, !Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_p140_fix_spaces_entail_wit_2_4 : p140_fix_spaces_entail_wit_2_4.
Proof.
  unfold p140_fix_spaces_entail_wit_2_4.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  rewrite (signed_last_nbits_eq (Znth i l 0) 8) by solve_ascii_range_char.
  Exists (((out_l_2 ++ cons 95 nil) ++ cons 95 nil) ++ cons (Znth i l 0) nil).
  entailer!.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_nonspace_pending2 i l ltac:(lia) ltac:(assumption) ltac:(solve_fix_pending))
      as [_ Hpend].
    symmetry; exact Hpend.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_nonspace_pending2 i l ltac:(lia) ltac:(assumption) ltac:(solve_fix_pending))
      as [Hp _].
    symmetry; exact Hp.
  - solve_list_nonzero_goal.
  - rewrite !Zlength_app, !Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_p140_fix_spaces_entail_wit_2_5 : p140_fix_spaces_entail_wit_2_5.
Proof.
  unfold p140_fix_spaces_entail_wit_2_5.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  rewrite (signed_last_nbits_eq (Znth i l 0) 8) by solve_ascii_range_char.
  Exists ((out_l_2 ++ cons 95 nil) ++ cons (Znth i l 0) nil).
  entailer!.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_nonspace_pending1 i l ltac:(lia) ltac:(assumption) ltac:(solve_fix_pending))
      as [_ Hpend].
    symmetry; exact Hpend.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_nonspace_pending1 i l ltac:(lia) ltac:(assumption) ltac:(solve_fix_pending))
      as [Hp _].
    symmetry; exact Hp.
  - solve_list_nonzero_goal.
  - rewrite !Zlength_app, !Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_p140_fix_spaces_return_wit_1 : p140_fix_spaces_return_wit_1.
Proof.
  unfold p140_fix_spaces_return_wit_1.
  intros.
  pre_process.
  assert (Hsp0 : spacelen = 0) by lia.
  Exists out_l_2 k_3.
  entailer!.
  - subst out_l_2.
    apply problem_140_spec_intro.
    + assumption.
    + 
    replace i with (Zlength l) by lia.
    symmetry.
    apply fix_spaces_output_pending0.
    match goal with
    | H : spacelen = fix_spaces_pending ?j l |- _ =>
        replace (fix_spaces_pending (Zlength l) l) with (fix_spaces_pending j l)
          by (replace j with (Zlength l) by lia; reflexivity);
        rewrite <- H; exact Hsp0
    | H : fix_spaces_pending ?j l = spacelen |- _ =>
        replace (fix_spaces_pending (Zlength l) l) with (fix_spaces_pending j l)
          by (replace j with (Zlength l) by lia; reflexivity);
        rewrite H; exact Hsp0
    end.
Qed.

Lemma proof_of_p140_fix_spaces_return_wit_2 : p140_fix_spaces_return_wit_2.
Proof.
  unfold p140_fix_spaces_return_wit_2.
  intros.
  pre_process.
  Exists (out_l_2 ++ cons 45 nil) (k_3 + 1).
  entailer!.
  subst out_l_2.
  apply problem_140_spec_intro.
  - assumption.
  -
    replace i with (Zlength l) by lia.
    symmetry.
    apply fix_spaces_output_pending_more with (p := spacelen).
    + replace (fix_spaces_pending (Zlength l) l)
        with (fix_spaces_pending i l) by (replace i with (Zlength l) by lia; reflexivity).
      match goal with
      | H : spacelen = fix_spaces_pending i l |- _ => exact H
      end.
    + lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - solve_list_nonzero_goal.
Qed.

Lemma proof_of_p140_fix_spaces_return_wit_3 : p140_fix_spaces_return_wit_3.
Proof.
  unfold p140_fix_spaces_return_wit_3.
  intros.
  pre_process.
  Exists ((out_l_2 ++ cons 95 nil) ++ cons 95 nil) ((k_3 + 1) + 1).
  entailer!.
  subst out_l_2 spacelen.
  apply problem_140_spec_intro.
  - assumption.
  -
    replace i with (Zlength l) by lia.
    symmetry.
    rewrite fix_spaces_output_pending2.
    2:{
      replace (fix_spaces_pending (Zlength l) l)
        with (fix_spaces_pending i l) by (replace i with (Zlength l) by lia; reflexivity).
      solve_fix_pending.
    }
    rewrite <- app_assoc.
    reflexivity.
  - rewrite !Zlength_app, !Zlength_cons, Zlength_nil. lia.
  - solve_list_nonzero_goal.
Qed.

Lemma proof_of_p140_fix_spaces_return_wit_4 : p140_fix_spaces_return_wit_4.
Proof.
  unfold p140_fix_spaces_return_wit_4.
  intros.
  pre_process.
  Exists (out_l_2 ++ cons 95 nil) (k_3 + 1).
  entailer!.
  subst out_l_2 spacelen.
  apply problem_140_spec_intro.
  - assumption.
  -
    replace i with (Zlength l) by lia.
    symmetry.
    apply fix_spaces_output_pending1.
    replace (fix_spaces_pending (Zlength l) l)
      with (fix_spaces_pending i l) by (replace i with (Zlength l) by lia; reflexivity).
    match goal with
    | H : 1 = fix_spaces_pending i l |- _ =>
        symmetry; exact H
    end.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - solve_list_nonzero_goal.
Qed.

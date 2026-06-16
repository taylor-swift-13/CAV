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
From SimpleC.EE.CAV.verify_20260607_164055_p142_sum_squares Require Import p142_sum_squares_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p142_sum_squares.
Local Open Scope sac.

Lemma transformed_sum_from_app : forall (xs ys : list Z) (start : Z),
  transformed_sum_from (xs ++ ys) start =
  transformed_sum_from xs start + transformed_sum_from ys (start + Zlength xs).
Proof.
  induction xs; intros ys start; simpl.
  - rewrite Zlength_nil.
    replace (start + 0) with start by lia.
    ring.
  - rewrite IHxs. rewrite Zlength_cons.
    replace (start + 1 + Zlength xs) with (start + (Zlength xs + 1)) by lia.
    ring.
Qed.

Lemma transformed_prefix_sum_0 : forall (l : list Z),
  transformed_prefix_sum 0 l = 0.
Proof.
  intro l. unfold transformed_prefix_sum, sublist. simpl. reflexivity.
Qed.

Lemma transformed_prefix_sum_step : forall (l : list Z) (i : Z),
  0 <= i < Zlength l ->
  transformed_prefix_sum (i + 1) l =
  transformed_prefix_sum i l + transformed_value i (Znth i l 0).
Proof.
  intros l i Hi.
  unfold transformed_prefix_sum.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single 0 i l) by lia.
  rewrite transformed_sum_from_app.
  rewrite Zlength_sublist by lia.
  replace (0 + (i - 0)) with i by lia.
  cbn [transformed_sum_from].
  fold (transformed_prefix_sum i l).
  ring.
Qed.

Lemma transformed_prefix_sum_full : forall (l : list Z),
  transformed_prefix_sum (Zlength l) l = transformed_sum_from l 0.
Proof.
  intro l.
  unfold transformed_prefix_sum.
  assert (H : sublist 0 (Zlength l) l = l).
  { unfold sublist.
    replace (Zlength l - 0) with (Zlength l) by lia.
    rewrite Zlength_correct, Nat2Z.id.
    cbn [Z.to_nat].
    rewrite skipn_O.
    apply firstn_all. }
  rewrite H. reflexivity.
Qed.

(* Use Z.eqb directly to avoid =? notation conflict with sac scope *)
Ltac unfold_tv_mod3_true H_rem3 :=
  (* Z.rem i 3 = 0: transformed_value = x*x *)
  assert (Htrue3 : Z.eqb (Z.rem _ 3) 0 = true) by (apply Z.eqb_eq; exact H_rem3);
  rewrite Htrue3; reflexivity.

Lemma proof_of_p142_sum_squares_safety_wit_6 : p142_sum_squares_safety_wit_6.
Proof.
  pre_process.
  (* H: i%3=0, H0: i<lst_size_pre, H1: 0<=lst_size_pre, H2: <INT_MAX,
     H3: =Zlength, H4: 0<=i, H5: i<=lst_size_pre, H6: sum_sq, H7: sum=tps *)
  unfold sum_squares_int_range in H6.
  destruct H6 as [Hrange _].
  assert (Hi : 0 <= i < Zlength input_l) by
    (split; [exact H4 | rewrite <- H3; exact H0]).
  specialize (Hrange i Hi). cbv beta in Hrange.
  destruct Hrange as [_ [_ Hstep]].
  assert (Htv : transformed_value i (Znth i input_l 0) = Znth i input_l 0 * Znth i input_l 0).
  { unfold transformed_value.
    assert (Htrue : Z.eqb (Z.rem i 3) 0 = true) by (apply Z.eqb_eq; exact H).
    rewrite Htrue. reflexivity. }
  rewrite Htv in Hstep. rewrite <- H7 in Hstep.
  clear H H0 H1 H2 H3 H4 H5 H7.
  split_pures.
  - dump_pre_spatial. exact (proj2 Hstep).
  - dump_pre_spatial. exact (proj1 Hstep).
Qed.

Lemma proof_of_p142_sum_squares_safety_wit_7 : p142_sum_squares_safety_wit_7.
Proof.
  pre_process.
  unfold sum_squares_int_range in H6.
  destruct H6 as [Hrange _].
  assert (Hi : 0 <= i < Zlength input_l) by
    (split; [exact H4 | rewrite <- H3; exact H0]).
  specialize (Hrange i Hi). cbv beta in Hrange.
  destruct Hrange as [Hsq _].
  clear H H0 H1 H2 H3 H4 H5 H7.
  split_pures.
  - dump_pre_spatial. exact (proj2 Hsq).
  - dump_pre_spatial. exact (proj1 Hsq).
Qed.

Lemma proof_of_p142_sum_squares_safety_wit_11 : p142_sum_squares_safety_wit_11.
Proof.
  pre_process.
  (* H: i%4=0, H0: i%3<>0, H1: i<lst_size_pre, H2: 0<=lst_size_pre,
     H3: <INT_MAX, H4: =Zlength, H5: 0<=i, H6: i<=lst_size_pre, H7: sum_sq, H8: sum=tps *)
  unfold sum_squares_int_range in H7.
  destruct H7 as [Hrange _].
  assert (Hi : 0 <= i < Zlength input_l) by
    (split; [exact H5 | rewrite <- H4; exact H1]).
  specialize (Hrange i Hi). cbv beta in Hrange.
  destruct Hrange as [_ [_ Hstep]].
  assert (Htv : transformed_value i (Znth i input_l 0) = Znth i input_l 0 * Znth i input_l 0 * Znth i input_l 0).
  { unfold transformed_value.
    assert (Hfalse3 : Z.eqb (Z.rem i 3) 0 = false) by (apply Z.eqb_neq; exact H0).
    assert (Htrue4  : Z.eqb (Z.rem i 4) 0 = true)  by (apply Z.eqb_eq;  exact H).
    rewrite Hfalse3, Htrue4. reflexivity. }
  rewrite Htv in Hstep. rewrite <- H8 in Hstep.
  clear H H0 H1 H2 H3 H4 H5 H6 H8.
  split_pures.
  - dump_pre_spatial. exact (proj2 Hstep).
  - dump_pre_spatial. exact (proj1 Hstep).
Qed.

Lemma proof_of_p142_sum_squares_safety_wit_12 : p142_sum_squares_safety_wit_12.
Proof.
  pre_process.
  unfold sum_squares_int_range in H7.
  destruct H7 as [Hrange _].
  assert (Hi : 0 <= i < Zlength input_l) by
    (split; [exact H5 | rewrite <- H4; exact H1]).
  specialize (Hrange i Hi). cbv beta in Hrange.
  destruct Hrange as [_ [Hcb _]].
  clear H H0 H1 H2 H3 H4 H5 H6 H8.
  split_pures.
  - dump_pre_spatial. exact (proj2 Hcb).
  - dump_pre_spatial. exact (proj1 Hcb).
Qed.

Lemma proof_of_p142_sum_squares_safety_wit_13 : p142_sum_squares_safety_wit_13.
Proof.
  pre_process.
  unfold sum_squares_int_range in H7.
  destruct H7 as [Hrange _].
  assert (Hi : 0 <= i < Zlength input_l) by
    (split; [exact H5 | rewrite <- H4; exact H1]).
  specialize (Hrange i Hi). cbv beta in Hrange.
  destruct Hrange as [Hsq _].
  clear H H0 H1 H2 H3 H4 H5 H6 H8.
  split_pures.
  - dump_pre_spatial. exact (proj2 Hsq).
  - dump_pre_spatial. exact (proj1 Hsq).
Qed.

Lemma proof_of_p142_sum_squares_safety_wit_17 : p142_sum_squares_safety_wit_17.
Proof.
  pre_process.
  (* H: i%4<>0, H0: i%3<>0 *)
  unfold sum_squares_int_range in H7.
  destruct H7 as [Hrange _].
  assert (Hi : 0 <= i < Zlength input_l) by
    (split; [exact H5 | rewrite <- H4; exact H1]).
  specialize (Hrange i Hi). cbv beta in Hrange.
  destruct Hrange as [_ [_ Hstep]].
  assert (Htv : transformed_value i (Znth i input_l 0) = Znth i input_l 0).
  { unfold transformed_value.
    assert (Hfalse3 : Z.eqb (Z.rem i 3) 0 = false) by (apply Z.eqb_neq; exact H0).
    assert (Hfalse4 : Z.eqb (Z.rem i 4) 0 = false) by (apply Z.eqb_neq; exact H).
    rewrite Hfalse3, Hfalse4. reflexivity. }
  rewrite Htv in Hstep. rewrite <- H8 in Hstep.
  clear H H0 H1 H2 H3 H4 H5 H6 H8.
  split_pures.
  - dump_pre_spatial. exact (proj2 Hstep).
  - dump_pre_spatial. exact (proj1 Hstep).
Qed.

Lemma proof_of_p142_sum_squares_entail_wit_1 : p142_sum_squares_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_p142_sum_squares_entail_wit_2_1 : p142_sum_squares_entail_wit_2_1.
Proof.
  pre_process.
  (* H: i%3=0, H0: i<lst_size_pre, H1: 0<=lst_size_pre, H2: <INT_MAX,
     H3: =Zlength, H4: 0<=i, H5: i<=lst_size_pre, H6: sum_sq, H7: sum=tps *)
  assert (Hi : 0 <= i < Zlength input_l) by
    (split; [exact H4 | rewrite <- H3; exact H0]).
  split_pure_spatial.
  - cancel (IntArray.full lst_pre lst_size_pre input_l).
  - split_pures.
    + dump_pre_spatial. exact H1.
    + dump_pre_spatial. exact H2.
    + dump_pre_spatial. exact H3.
    + clear H. dump_pre_spatial. lia.
    + clear H. dump_pre_spatial. lia.
    + clear H. dump_pre_spatial. exact H6.
    + dump_pre_spatial.
      rewrite (transformed_prefix_sum_step input_l i Hi).
      assert (Htv : transformed_value i (Znth i input_l 0) = Znth i input_l 0 * Znth i input_l 0).
      { unfold transformed_value.
        assert (Htrue3 : Z.eqb (Z.rem i 3) 0 = true) by (apply Z.eqb_eq; exact H).
        rewrite Htrue3. reflexivity. }
      rewrite Htv. rewrite <- H7. ring.
Qed.

Lemma proof_of_p142_sum_squares_entail_wit_2_2 : p142_sum_squares_entail_wit_2_2.
Proof.
  pre_process.
  (* H: i%4=0, H0: i%3<>0, H1: i<lst_size_pre, H2: 0<=lst_size_pre,
     H3: <INT_MAX, H4: =Zlength, H5: 0<=i, H6: i<=lst_size_pre,
     H7: sum_sq, H8: sum=tps *)
  assert (Hi : 0 <= i < Zlength input_l) by
    (split; [exact H5 | rewrite <- H4; exact H1]).
  split_pure_spatial.
  - cancel (IntArray.full lst_pre lst_size_pre input_l).
  - split_pures.
    + dump_pre_spatial. exact H2.
    + dump_pre_spatial. exact H3.
    + dump_pre_spatial. exact H4.
    + clear H H0. dump_pre_spatial. lia.
    + clear H H0. dump_pre_spatial. lia.
    + clear H H0. dump_pre_spatial. exact H7.
    + dump_pre_spatial.
      rewrite (transformed_prefix_sum_step input_l i Hi).
      assert (Htv : transformed_value i (Znth i input_l 0) = Znth i input_l 0 * Znth i input_l 0 * Znth i input_l 0).
      { unfold transformed_value.
        assert (Hfalse3 : Z.eqb (Z.rem i 3) 0 = false) by (apply Z.eqb_neq; exact H0).
        assert (Htrue4  : Z.eqb (Z.rem i 4) 0 = true)  by (apply Z.eqb_eq;  exact H).
        rewrite Hfalse3, Htrue4. reflexivity. }
      rewrite Htv. rewrite <- H8. ring.
Qed.

Lemma proof_of_p142_sum_squares_entail_wit_2_3 : p142_sum_squares_entail_wit_2_3.
Proof.
  pre_process.
  (* H: i%4<>0, H0: i%3<>0, H1: i<lst_size_pre, H2: 0<=lst_size_pre,
     H3: <INT_MAX, H4: =Zlength, H5: 0<=i, H6: i<=lst_size_pre,
     H7: sum_sq, H8: sum=tps *)
  assert (Hi : 0 <= i < Zlength input_l) by
    (split; [exact H5 | rewrite <- H4; exact H1]).
  split_pure_spatial.
  - cancel (IntArray.full lst_pre lst_size_pre input_l).
  - split_pures.
    + dump_pre_spatial. exact H2.
    + dump_pre_spatial. exact H3.
    + dump_pre_spatial. exact H4.
    + clear H H0. dump_pre_spatial. lia.
    + clear H H0. dump_pre_spatial. lia.
    + clear H H0. dump_pre_spatial. exact H7.
    + dump_pre_spatial.
      rewrite (transformed_prefix_sum_step input_l i Hi).
      assert (Htv : transformed_value i (Znth i input_l 0) = Znth i input_l 0).
      { unfold transformed_value.
        assert (Hfalse3 : Z.eqb (Z.rem i 3) 0 = false) by (apply Z.eqb_neq; exact H0).
        assert (Hfalse4 : Z.eqb (Z.rem i 4) 0 = false) by (apply Z.eqb_neq; exact H).
        rewrite Hfalse3, Hfalse4. reflexivity. }
      rewrite Htv. rewrite <- H8. ring.
Qed.

Lemma proof_of_p142_sum_squares_return_wit_1 : p142_sum_squares_return_wit_1.
Proof.
  pre_process.
  (* H: i>=lst_size_pre, H0: 0<=lst_size_pre, H1: <INT_MAX, H2: =Zlength,
     H3: 0<=i, H4: i<=lst_size_pre, H5: sum_sq, H6: sum=tps *)
  split_pure_spatial.
  - cancel (IntArray.full lst_pre lst_size_pre input_l).
  - dump_pre_spatial.
    unfold problem_142_spec.
    rewrite H6.
    replace i with lst_size_pre by lia.
    rewrite H2.
    apply transformed_prefix_sum_full.
Qed.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p130_tri Require Import p130_tri_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Arith.
Require Import List.

Import naive_C_Rules.
Require Import p130_tri.
Local Open Scope sac.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Local Open Scope list_scope.

(* Proof helpers moved from p130_tri.v so public contract files expose definitions only. *)

Lemma tri_sequence_Zlength : forall n,
  0 <= n ->
  Zlength (tri_sequence n) = n + 1.
Proof.
  intros n Hn.
  unfold tri_sequence.
  rewrite Zlength_correct.
  rewrite length_map, Zseq_length.
  lia.
Qed.
Lemma tri_sequence_Znth : forall n i,
  0 <= i <= n ->
  Znth i (tri_sequence n) 0 = tri i.
Proof.
  intros n i Hi.
  unfold tri_sequence, Znth.
  rewrite (@nth_indep Z
            (map tri (Zseq 0 (Z.to_nat (n + 1)))) (Z.to_nat i)
            0 (tri 0)).
  2:{
    rewrite length_map, Zseq_length.
    lia.
  }
  rewrite map_nth with (d := 0%Z).
  rewrite Zseq_nth by lia.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma tri_sequence_sublist_snoc : forall n i,
  0 <= i <= n ->
  sublist 0 (i + 1) (tri_sequence n) =
  sublist 0 i (tri_sequence n) ++ tri i :: nil.
Proof.
  intros n i Hi.
  pose proof (tri_sequence_Zlength n ltac:(lia)) as Hlen.
  rewrite (sublist_split 0 (i + 1) i).
  - rewrite (sublist_single 0 i (tri_sequence n)).
    + rewrite tri_sequence_Znth by lia.
      reflexivity.
    + rewrite Hlen. lia.
  - lia.
  - rewrite Hlen. lia.
Qed.
Lemma tri_sequence_sublist_Znth : forall n i j,
  0 <= j < i ->
  i <= n + 1 ->
  Znth (j - 0) (sublist 0 i (tri_sequence n)) 0 = tri j.
Proof.
  intros n i j Hj Hi.
  replace (j - 0) with j by lia.
  rewrite Znth_sublist0 by lia.
  apply tri_sequence_Znth.
  lia.
Qed.
Lemma tri_fuel_stable_ge : forall fuel i,
  0 <= i ->
  (Z.to_nat i <= fuel)%nat ->
  tri_fuel fuel i = tri i.
Proof.
  intro fuel.
  pattern fuel.
  apply lt_wf_ind.
  clear fuel.
  intros fuel IH i Hi Hle.
  unfold tri.
  destruct fuel as [|fuel'].
  - assert (i = 0) by lia.
    subst; reflexivity.
  - destruct (Z.to_nat i) as [|ki] eqn:Hki.
    + assert (i = 0) by lia.
      subst; reflexivity.
    + simpl.
      destruct (Z.eqb i 0) eqn:Hi0.
      { reflexivity. }
      destruct (Z.eqb i 1) eqn:Hi1.
      { reflexivity. }
      destruct (Z.even i) eqn:Hiev.
      { reflexivity. }
      apply Z.eqb_neq in Hi0.
      apply Z.eqb_neq in Hi1.
      rewrite (IH fuel' ltac:(lia) (i - 2)).
      2: lia.
      2: {
        rewrite Z2Nat.inj_sub by lia.
        rewrite Hki.
        lia.
      }
      rewrite (IH ki ltac:(lia) (i - 2)).
      2: lia.
      2: {
        rewrite Z2Nat.inj_sub by lia.
        rewrite Hki.
        lia.
      }
      reflexivity.
Qed.
Lemma tri_even_quot_by_even : forall i,
  2 <= i ->
  Z.even i = true ->
  tri i = 1 + Z.quot i 2.
Proof.
  intros i Hi Heven.
  unfold tri.
  destruct (Z.to_nat i) as [|fuel] eqn:Hfuel; [lia|].
  cbn [tri_fuel].
  destruct (Z.eqb i 0) eqn:Hi0; [apply Z.eqb_eq in Hi0; lia|].
  destruct (Z.eqb i 1) eqn:Hi1; [apply Z.eqb_eq in Hi1; lia|].
  rewrite Heven.
  reflexivity.
Qed.
Lemma tri_even_quot : forall i,
  2 <= i ->
  Z.rem i 2 = 0 ->
  tri i = 1 + Z.quot i 2.
Proof.
  intros i Hi Hrem.
  apply tri_even_quot_by_even; [lia|].
  apply Z.even_spec.
  exists (Z.quot i 2).
  pose proof (Z.quot_rem' i 2).
  lia.
Qed.
Lemma tri_odd_quot : forall i,
  2 <= i ->
  Z.rem i 2 <> 0 ->
  tri i = tri (i - 1) + tri (i - 2) + 1 + Z.quot (i + 1) 2.
Proof.
  intros i Hi Hrem.
  assert (Hodd : Z.even i = false).
  {
    destruct (Z.even i) eqn:Heven; [|reflexivity].
    apply Z.even_spec in Heven.
    destruct Heven as [q Hq].
    exfalso.
    apply Hrem.
    rewrite Hq.
    replace (2 * q) with (q * 2) by lia.
    rewrite Z.rem_mul; lia.
  }
  assert (Hi_ge3 : 3 <= i).
  {
    assert (i <> 2) by (intro Hcontra; subst; apply Hrem; reflexivity).
    lia.
  }
  unfold tri at 1.
  destruct (Z.to_nat i) as [|fuel] eqn:Hfuel; [lia|].
  cbn [tri_fuel].
  destruct (Z.eqb i 0) eqn:Hi0; [apply Z.eqb_eq in Hi0; lia|].
  destruct (Z.eqb i 1) eqn:Hi1; [apply Z.eqb_eq in Hi1; lia|].
  rewrite Hodd.
  replace (tri_fuel fuel (i - 2)) with (tri (i - 2)).
  2:{
    symmetry.
    apply tri_fuel_stable_ge; [lia|].
    rewrite Z2Nat.inj_sub by lia.
    rewrite Hfuel.
    lia.
  }
  replace (1 + Z.quot (i - 1) 2) with (tri (i - 1)).
  2:{
    rewrite tri_even_quot_by_even; [reflexivity|lia|].
    replace (i - 1) with (i + -1) by lia.
    rewrite Z.even_add.
    rewrite Hodd.
    reflexivity.
  }
  ring.
Qed.
Lemma tri_fuel_nonneg : forall fuel i,
  0 <= i ->
  0 <= tri_fuel fuel i.
Proof.
  induction fuel; intros i Hi; cbn [tri_fuel].
  - destruct (Z.eqb i 1); lia.
  - destruct (Z.eqb i 0) eqn:Hi0; [lia|].
    destruct (Z.eqb i 1) eqn:Hi1; [lia|].
    apply Z.eqb_neq in Hi0.
    apply Z.eqb_neq in Hi1.
    destruct (Z.even i); [pose proof (Z.quot_pos i 2 ltac:(lia) ltac:(lia)); lia|].
    pose proof (IHfuel (i - 2) ltac:(lia)).
    pose proof (Z.quot_pos (i - 1) 2 ltac:(lia) ltac:(lia)).
    pose proof (Z.quot_pos (i + 1) 2 ltac:(lia) ltac:(lia)).
    lia.
Qed.
Lemma tri_nonneg : forall i,
  0 <= i ->
  0 <= tri i.
Proof.
  intros i Hi.
  unfold tri.
  apply tri_fuel_nonneg.
  exact Hi.
Qed.
Lemma tri_even_expr_range : forall n i,
  tri_seq_int_range n ->
  2 <= i <= n ->
  INT_MIN <= 1 + Z.quot i 2 <= INT_MAX.
Proof.
  intros n i Hrange Hi.
  destruct Hrange as [_ Hstep].
  pose proof (Hstep i Hi) as [H _].
  exact H.
Qed.
Lemma tri_odd_expr_range : forall n i,
  tri_seq_int_range n ->
  2 <= i <= n ->
  INT_MIN <= tri (i - 1) + tri (i - 2) + 1 + Z.quot (i + 1) 2 <= INT_MAX.
Proof.
  intros n i Hrange Hi.
  destruct Hrange as [_ Hstep].
  pose proof (Hstep i Hi) as [_ H].
  exact H.
Qed.
Lemma tri_odd_expr_partial_range_1 : forall n i,
  tri_seq_int_range n ->
  2 <= i <= n ->
  INT_MIN <= tri (i - 1) + tri (i - 2) <= INT_MAX.
Proof.
  intros n i Hrange Hi.
  pose proof (tri_odd_expr_range n i Hrange Hi) as Hfull.
  pose proof (tri_nonneg (i - 1) ltac:(lia)).
  pose proof (tri_nonneg (i - 2) ltac:(lia)).
  assert (0 <= Z.quot (i + 1) 2) by (apply Z.quot_pos; lia).
  lia.
Qed.
Lemma tri_odd_expr_partial_range_2 : forall n i,
  tri_seq_int_range n ->
  2 <= i <= n ->
  INT_MIN <= tri (i - 1) + tri (i - 2) + 1 <= INT_MAX.
Proof.
  intros n i Hrange Hi.
  pose proof (tri_odd_expr_range n i Hrange Hi) as Hfull.
  pose proof (tri_nonneg (i - 1) ltac:(lia)).
  pose proof (tri_nonneg (i - 2) ltac:(lia)).
  assert (0 <= Z.quot (i + 1) 2) by (apply Z.quot_pos; lia).
  lia.
Qed.
Lemma tri_sequence_even_snoc : forall n i,
  2 <= i <= n ->
  Z.rem i 2 = 0 ->
  sublist 0 (i + 1) (tri_sequence n) =
  sublist 0 i (tri_sequence n) ++ (1 + Z.quot i 2) :: nil.
Proof.
  intros n i Hi Hrem.
  rewrite tri_sequence_sublist_snoc by lia.
  rewrite tri_even_quot by lia.
  reflexivity.
Qed.
Lemma tri_sequence_odd_snoc : forall n i,
  2 <= i <= n ->
  Z.rem i 2 <> 0 ->
  sublist 0 (i + 1) (tri_sequence n) =
  sublist 0 i (tri_sequence n) ++
  (Znth (i - 1 - 0) (sublist 0 i (tri_sequence n)) 0 +
   Znth (i - 2 - 0) (sublist 0 i (tri_sequence n)) 0 +
   1 + Z.quot (i + 1) 2) :: nil.
Proof.
  intros n i Hi Hrem.
  rewrite tri_sequence_sublist_snoc by lia.
  rewrite tri_odd_quot by lia.
  rewrite !tri_sequence_sublist_Znth by lia.
  reflexivity.
Qed.
Lemma tri_sequence_sublist_2 : forall n,
  1 <= n ->
  sublist 0 2 (tri_sequence n) = 1 :: 3 :: nil.
Proof.
  intros n Hn.
  rewrite tri_sequence_sublist_snoc with (i := 1) by lia.
  rewrite tri_sequence_sublist_snoc with (i := 0) by lia.
  unfold sublist.
  simpl.
  reflexivity.
Qed.
Lemma tri_sequence_spec : forall n,
  0 <= n ->
  problem_130_spec n (tri_sequence n).
Proof.
  intros n Hn.
  unfold problem_130_spec.
  split; auto.
Qed.
Lemma tri_seq_int_range_value : forall n i,
  tri_seq_int_range n ->
  0 <= i <= n ->
  INT_MIN <= tri i <= INT_MAX.
Proof.
  intros n i [Hrange _] Hi.
  apply Hrange; lia.
Qed.
Lemma tri_seq_int_range_step : forall n i,
  tri_seq_int_range n ->
  2 <= i <= n ->
  INT_MIN <= 1 + Z.quot i 2 <= INT_MAX /\
  INT_MIN <= tri (i - 1) + tri (i - 2) + 1 + Z.quot (i + 1) 2 <= INT_MAX.
Proof.
  intros n i [_ Hstep] Hi.
  apply Hstep; lia.
Qed.


Lemma proof_of_p130_tri_safety_wit_14 : p130_tri_safety_wit_14.
Proof.
  pre_process.
  pose proof (tri_even_expr_range n0 i H6 ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_p130_tri_safety_wit_18 : p130_tri_safety_wit_18.
Proof.
  pre_process.
  rewrite !tri_sequence_sublist_Znth by lia.
  pose proof (tri_odd_expr_range n0 i H6 ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_p130_tri_safety_wit_21 : p130_tri_safety_wit_21.
Proof.
  pre_process.
  rewrite !tri_sequence_sublist_Znth by lia.
  pose proof (tri_odd_expr_partial_range_2 n0 i H6 ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_p130_tri_safety_wit_22 : p130_tri_safety_wit_22.
Proof.
  pre_process.
  rewrite !tri_sequence_sublist_Znth by lia.
  pose proof (tri_odd_expr_partial_range_1 n0 i H6 ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_p130_tri_entail_wit_1 : p130_tri_entail_wit_1.
Proof.
  pre_process.
  subst.
  rewrite tri_sequence_Zlength by lia.
  rewrite tri_sequence_sublist_2 by lia.
  sep_apply (IntArray.seg_single retval_2 1 3).
  sep_apply (IntArray.seg_single retval_2 0 1).
  sep_apply (IntArray.seg_merge_to_seg retval_2 0 1 2); [ | lia].
  entailer!.
Qed.

Lemma proof_of_p130_tri_entail_wit_2_1 : p130_tri_entail_wit_2_1.
Proof.
  pre_process.
  rewrite tri_sequence_even_snoc by lia.
  entailer!.
Qed.

Lemma proof_of_p130_tri_entail_wit_2_2 : p130_tri_entail_wit_2_2.
Proof.
  pre_process.
  rewrite tri_sequence_odd_snoc by lia.
  entailer!.
Qed.

Lemma proof_of_p130_tri_return_wit_1 : p130_tri_return_wit_1.
Proof.
  pre_process.
  replace i with (n0 + 1) in * by lia.
  Exists (tri_sequence n0) (n0 + 1) data_2.
  entailer!.
  - rewrite sublist_self by (rewrite tri_sequence_Zlength by lia; lia).
    sep_apply (IntArray.seg_to_full data_2 0 (n0 + 1)).
    replace (data_2 + 0 * sizeof (INT)) with data_2 by lia.
    replace (n0 + 1 - 0) with (n0 + 1) by lia.
    rewrite (IntArray.undef_seg_empty data_2 (n0 + 1)).
    entailer!.
  - apply tri_sequence_spec.
    lia.
Qed.

Lemma proof_of_p130_tri_return_wit_2 : p130_tri_return_wit_2.
Proof.
  pre_process.
  Exists (tri_sequence n0) (n0 + 1) retval_2.
  entailer!.
  - replace n0 with 0 in * by lia.
    subst n_pre.
    replace (tri_sequence 0) with (1 :: nil) by reflexivity.
    sep_apply (IntArray.seg_single retval_2 0 1).
    sep_apply (IntArray.seg_to_full retval_2 0 1).
    replace (retval_2 + 0 * sizeof (INT)) with retval_2 by lia.
    replace (1 - 0) with 1 by lia.
    rewrite (IntArray.undef_seg_empty retval_2 1).
    entailer!.
  - apply tri_sequence_spec.
    lia.
  - rewrite tri_sequence_Zlength by lia.
    lia.
Qed.

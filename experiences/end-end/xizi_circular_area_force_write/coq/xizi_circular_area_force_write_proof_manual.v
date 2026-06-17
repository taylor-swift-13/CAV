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
From SimpleC.EE.CAV.verify_20260602_212502v_xizi_circular_area_force_write Require Import xizi_circular_area_force_write_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma length_replace_nth :
  forall {A : Type} (n : nat) (x : A) (l : list A),
    length (replace_nth n l x) = length l.
Proof.
  intros A n x l.
  revert n.
  induction l; intros n; destruct n; simpl; auto.
Qed.

Lemma nth_replace_nth_same :
  forall {A : Type} (n : nat) (x d : A) (l : list A),
    (n < length l)%nat ->
    nth n (replace_nth n l x) d = x.
Proof.
  intros A n x d l.
  revert n.
  induction l as [|a l IH]; intros [|n] Hlt; simpl in *.
  - inversion Hlt.
  - inversion Hlt.
  - reflexivity.
  - apply IH. lia.
Qed.

Lemma nth_replace_nth_diff :
  forall {A : Type} (k n : nat) (x d : A) (l : list A),
    k <> n ->
    nth k (replace_nth n l x) d = nth k l d.
Proof.
  intros A k n x d l.
  revert k n.
  induction l; intros k n Hneq; destruct k, n; simpl; auto; try contradiction.
Qed.

Lemma Znth_replace_Znth_same :
  forall {A : Type} (i : Z) (x d : A) (l : list A),
    0 <= i < Zlength l ->
    Znth i (replace_Znth i x l) d = x.
Proof.
  intros A i x d l Hi.
  unfold Znth, replace_Znth.
  apply nth_replace_nth_same.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma Znth_replace_Znth_diff :
  forall {A : Type} (k i : Z) (x d : A) (l : list A),
    0 <= k < Zlength l ->
    0 <= i ->
    k <> i ->
    Znth k (replace_Znth i x l) d = Znth k l d.
Proof.
  intros A k i x d l Hk Hi Hneq.
  unfold Znth, replace_Znth.
  apply nth_replace_nth_diff.
  lia.
Qed.

Lemma proof_of_xizi_circular_area_force_write_return_wit_1 : xizi_circular_area_force_write_return_wit_1.
Proof.
  pre_process.
  set (w := Z.rem (Znth 1 l 0 + data_length_pre) area_length_pre).
  Exists (replace_Znth 0 w
    (replace_Znth 2 1
      (replace_Znth 1 w l))).
  entailer!.
  - intros Hforce.
    repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_same 0 w 0
      (replace_Znth 2 1 (replace_Znth 1 w l)))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_diff 1 0 w 0
      (replace_Znth 2 1 (replace_Znth 1 w l)))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_diff 1 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_same 1 w 0 l) by lia.
    reflexivity.
  - repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_diff 2 0 w 0
      (replace_Znth 2 1 (replace_Znth 1 w l)))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_same 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    reflexivity.
  - intro Heq.
    repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_diff 1 0 w 0
      (replace_Znth 2 1 (replace_Znth 1 w l)))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_diff 1 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_same 1 w 0 l) by lia.
    unfold w.
    rewrite Heq.
    rewrite Z.rem_same by lia.
    reflexivity.
  - intro Hlt.
    repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_diff 1 0 w 0
      (replace_Znth 2 1 (replace_Znth 1 w l)))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_diff 1 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_same 1 w 0 l) by lia.
    unfold w.
    rewrite Z.rem_small by lia.
    reflexivity.
  - repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_diff 1 0 w 0
      (replace_Znth 2 1 (replace_Znth 1 w l)))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_diff 1 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_same 1 w 0 l) by lia.
    unfold w.
    apply Z.rem_bound_pos; lia.
  - repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_diff 1 0 w 0
      (replace_Znth 2 1 (replace_Znth 1 w l)))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_diff 1 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_same 1 w 0 l) by lia.
    unfold w.
    apply Z.rem_nonneg; lia.
  - repeat rewrite Zlength_replace_Znth in *.
    lia.
Qed.

Lemma proof_of_xizi_circular_area_force_write_return_wit_2 : xizi_circular_area_force_write_return_wit_2.
Proof.
  pre_process.
  set (w := data_length_pre - (area_length_pre - Znth 1 l 0)).
  Exists (replace_Znth 0 w
    (replace_Znth 2 1
      (replace_Znth 1 w l))).
  entailer!.
  - intros Hforce.
    repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_same 0 w 0
      (replace_Znth 2 1 (replace_Znth 1 w l)))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_diff 1 0 w 0
      (replace_Znth 2 1 (replace_Znth 1 w l)))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_diff 1 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_same 1 w 0 l) by lia.
    lia.
  - repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_diff 2 0 w 0
      (replace_Znth 2 1 (replace_Znth 1 w l)))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_same 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    reflexivity.
  - intro Hgt.
    repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_diff 1 0 w 0
      (replace_Znth 2 1 (replace_Znth 1 w l)))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_diff 1 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_same 1 w 0 l) by lia.
    unfold w.
    lia.
  - repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_diff 1 0 w 0
      (replace_Znth 2 1 (replace_Znth 1 w l)))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_diff 1 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_same 1 w 0 l) by lia.
    unfold w.
    lia.
  - repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_diff 1 0 w 0
      (replace_Znth 2 1 (replace_Znth 1 w l)))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_diff 1 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_same 1 w 0 l) by lia.
    unfold w.
    lia.
  - repeat rewrite Zlength_replace_Znth in *.
    lia.
Qed.

Lemma proof_of_xizi_circular_area_force_write_return_wit_3 : xizi_circular_area_force_write_return_wit_3.
Proof.
  pre_process.
  set (w := data_length_pre - (area_length_pre - Znth 1 l 0)).
  Exists (replace_Znth 2 1
    (replace_Znth 1 w l)).
  entailer!.
  - intros Hforce_zero.
    repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_diff 0 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_diff 0 1 w 0 l)
      by lia.
    reflexivity.
  - repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_same 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    reflexivity.
  - intro Hgt.
    repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_diff 1 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_same 1 w 0 l) by lia.
    unfold w.
    lia.
  - repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_diff 1 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_same 1 w 0 l) by lia.
    unfold w.
    lia.
  - repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_diff 1 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_same 1 w 0 l) by lia.
    unfold w.
    lia.
  - repeat rewrite Zlength_replace_Znth in *.
    lia.
Qed.

Lemma proof_of_xizi_circular_area_force_write_return_wit_4 : xizi_circular_area_force_write_return_wit_4.
Proof.
  pre_process.
  set (w := Z.rem (Znth 1 l 0 + data_length_pre) area_length_pre).
  Exists (replace_Znth 2 1
    (replace_Znth 1 w l)).
  entailer!.
  - intros Hforce_zero.
    repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_diff 0 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_diff 0 1 w 0 l)
      by lia.
    reflexivity.
  - repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_same 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    reflexivity.
  - intro Heq.
    repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_diff 1 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_same 1 w 0 l) by lia.
    unfold w.
    rewrite Heq.
    rewrite Z.rem_same by lia.
    reflexivity.
  - intro Hlt.
    repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_diff 1 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_same 1 w 0 l) by lia.
    unfold w.
    rewrite Z.rem_small by lia.
    reflexivity.
  - repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_diff 1 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_same 1 w 0 l) by lia.
    unfold w.
    apply Z.rem_bound_pos; lia.
  - repeat rewrite Zlength_replace_Znth in *.
    rewrite (Znth_replace_Znth_diff 1 2 1 0
      (replace_Znth 1 w l))
      by (rewrite ?Zlength_replace_Znth in *; lia).
    rewrite (Znth_replace_Znth_same 1 w 0 l) by lia.
    unfold w.
    apply Z.rem_nonneg; lia.
  - repeat rewrite Zlength_replace_Znth in *.
    lia.
Qed.

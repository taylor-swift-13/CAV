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
From SimpleC.EE.CAV.ground_truth_p091_is_bored Require Import p091_is_bored_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List Coq.Arith.Arith.

Import naive_C_Rules.
Require Import p091_is_bored.
Local Open Scope sac.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope list_scope.

(* Proof helpers moved from p091_is_bored.v so public contract files expose definitions only. *)

Lemma z_to_nat_Zlength : forall (l : list Z),
  Z.to_nat (Zlength l) = Datatypes.length l.
Proof.
  intros l.
  rewrite Zlength_correct.
  lia.
Qed.
Lemma bored_state_after_step : forall i l sum isstart isi,
  0 <= i ->
  bored_state_after_nat (Z.to_nat i) l = (sum, isstart, isi) ->
  bored_state_after_nat (Z.to_nat (i + 1)) l =
    (sum + bored_add (Znth i l 0) isi,
     bored_next_isstart (Znth i l 0) isstart,
     bored_next_isi (Znth i l 0) isstart).
Proof.
  intros i l sum isstart isi Hi Hstate.
  rewrite Z2Nat.inj_add by lia.
  change (Z.to_nat 1) with 1%nat.
  rewrite Nat.add_1_r.
  simpl.
  rewrite Z2Nat.id by lia.
  rewrite Hstate.
  reflexivity.
Qed.
Lemma bored_sum_prefix_step : forall i l,
  0 <= i ->
  bored_sum_prefix (i + 1) l =
  bored_sum_prefix i l +
  bored_add (Znth i l 0) (bored_isi_prefix i l).
Proof.
  intros i l Hi.
  unfold bored_sum_prefix, bored_isi_prefix.
  destruct (bored_state_after_nat (Z.to_nat i) l) as [[sum isstart] isi] eqn:Hstate.
  rewrite (bored_state_after_step i l sum isstart isi Hi Hstate).
  reflexivity.
Qed.
Lemma bored_isstart_prefix_step : forall i l,
  0 <= i ->
  bored_isstart_prefix (i + 1) l =
  bored_next_isstart (Znth i l 0) (bored_isstart_prefix i l).
Proof.
  intros i l Hi.
  unfold bored_isstart_prefix.
  destruct (bored_state_after_nat (Z.to_nat i) l) as [[sum isstart] isi] eqn:Hstate.
  rewrite (bored_state_after_step i l sum isstart isi Hi Hstate).
  reflexivity.
Qed.
Lemma bored_isi_prefix_step : forall i l,
  0 <= i ->
  bored_isi_prefix (i + 1) l =
  bored_next_isi (Znth i l 0) (bored_isstart_prefix i l).
Proof.
  intros i l Hi.
  unfold bored_isi_prefix, bored_isstart_prefix.
  destruct (bored_state_after_nat (Z.to_nat i) l) as [[sum isstart] isi] eqn:Hstate.
  rewrite (bored_state_after_step i l sum isstart isi Hi Hstate).
  reflexivity.
Qed.
Lemma bored_state_list_app : forall l1 l2 st,
  bored_state_list (l1 ++ l2) st =
  bored_state_list l2 (bored_state_list l1 st).
Proof.
  induction l1 as [| c rest IH]; intros l2 st; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma bored_state_list_snoc : forall l c st,
  bored_state_list (l ++ [c]) st =
  bored_step_z_state (bored_state_list l st) c.
Proof.
  intros l c st.
  rewrite bored_state_list_app.
  reflexivity.
Qed.
Lemma firstn_succ_snoc_91 : forall {A : Type} n (l : list A) d,
  (n < Datatypes.length l)%nat ->
  firstn (S n) l = List.app (firstn n l) [nth n l d].
Proof.
  induction n as [| n IH]; intros l d Hn.
  - destruct l; simpl in *; try lia. reflexivity.
  - destruct l; simpl in *; try lia.
    rewrite (IH l d) by lia. reflexivity.
Qed.
Lemma Znth_of_nat_nth_91 : forall {A : Type} (l : list A) n d,
  (n < Datatypes.length l)%nat ->
  Znth (Z.of_nat n) l d = nth n l d.
Proof.
  intros A l n d Hn.
  unfold Znth.
  rewrite Nat2Z.id.
  reflexivity.
Qed.
Lemma bored_state_after_nat_firstn : forall n l,
  (n <= Datatypes.length l)%nat ->
  bored_state_after_nat n l =
  bored_state_list (firstn n l) (0, 1, 0).
Proof.
  induction n as [| n IH]; intros l Hn.
  - reflexivity.
  - cbn [bored_state_after_nat].
    rewrite IH by lia.
    rewrite firstn_succ_snoc_91 with (d := 0) by lia.
    rewrite bored_state_list_snoc.
    rewrite Znth_of_nat_nth_91 by lia.
    destruct (bored_state_list (firstn n l) (0, 1, 0)) as [[sum isstart] isi].
    reflexivity.
Qed.
Lemma problem_91_spec_intro : forall s output,
  output = bored_sum_prefix (Zlength s) s ->
  problem_91_spec s output.
Proof.
  intros s output Hout.
  unfold problem_91_spec, bored_sum_prefix in *.
  rewrite Hout.
  rewrite z_to_nat_Zlength.
  rewrite bored_state_after_nat_firstn by lia.
  rewrite firstn_all.
  destruct (bored_state_list s (0, 1, 0)) as [[sum isstart] isi].
  reflexivity.
Qed.


Ltac bored_pre :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia.

Ltac simplify_zeqb :=
  repeat match goal with
  | H : ?x = ?y |- context[Z.eqb ?x ?y] =>
      replace (Z.eqb x y) with true by (symmetry; apply Z.eqb_eq; lia)
  | H : ?x = ?y |- context[Z.eqb ?y ?x] =>
      replace (Z.eqb y x) with true by (symmetry; apply Z.eqb_eq; lia)
  | H : ?x <> ?y |- context[Z.eqb ?x ?y] =>
      replace (Z.eqb x y) with false by (symmetry; apply Z.eqb_neq; lia)
  | H : ?x <> ?y |- context[Z.eqb ?y ?x] =>
      replace (Z.eqb y x) with false by (symmetry; apply Z.eqb_neq; lia)
  | |- context[Z.eqb ?x ?x] =>
      replace (Z.eqb x x) with true by (symmetry; apply Z.eqb_eq; lia)
  end;
  simpl.

Ltac unfold_bored_step :=
  repeat rewrite bored_sum_prefix_step by lia;
  repeat rewrite bored_isstart_prefix_step by lia;
  repeat rewrite bored_isi_prefix_step by lia;
  unfold bored_add, bored_next_isstart, bored_next_isi,
         z_is_space, z_is_i, z_is_delim, zbool in *;
  simplify_zeqb.

Ltac solve_bored_step :=
  bored_pre;
  unfold_bored_step;
  entailer!;
  try lia.

Lemma proof_of_p091_is_bored_entail_wit_1 : p091_is_bored_entail_wit_1.
Proof.
  unfold p091_is_bored_entail_wit_1.
  intros.
  bored_pre.
  unfold bored_sum_prefix, bored_isstart_prefix, bored_isi_prefix.
  simpl.
  entailer!.
Qed.

Lemma proof_of_p091_is_bored_entail_wit_2_1 : p091_is_bored_entail_wit_2_1.
Proof. unfold p091_is_bored_entail_wit_2_1; intros; solve_bored_step. Qed.

Lemma proof_of_p091_is_bored_entail_wit_2_2 : p091_is_bored_entail_wit_2_2.
Proof. unfold p091_is_bored_entail_wit_2_2; intros; solve_bored_step. Qed.

Lemma proof_of_p091_is_bored_entail_wit_2_3 : p091_is_bored_entail_wit_2_3.
Proof. unfold p091_is_bored_entail_wit_2_3; intros; solve_bored_step. Qed.

Lemma proof_of_p091_is_bored_entail_wit_2_4 : p091_is_bored_entail_wit_2_4.
Proof. unfold p091_is_bored_entail_wit_2_4; intros; solve_bored_step. Qed.

Lemma proof_of_p091_is_bored_entail_wit_2_5 : p091_is_bored_entail_wit_2_5.
Proof. unfold p091_is_bored_entail_wit_2_5; intros; solve_bored_step. Qed.

Lemma proof_of_p091_is_bored_entail_wit_2_6 : p091_is_bored_entail_wit_2_6.
Proof. unfold p091_is_bored_entail_wit_2_6; intros; solve_bored_step. Qed.

Lemma proof_of_p091_is_bored_entail_wit_2_7 : p091_is_bored_entail_wit_2_7.
Proof. unfold p091_is_bored_entail_wit_2_7; intros; solve_bored_step. Qed.

Lemma proof_of_p091_is_bored_entail_wit_2_8 : p091_is_bored_entail_wit_2_8.
Proof. unfold p091_is_bored_entail_wit_2_8; intros; solve_bored_step. Qed.

Lemma proof_of_p091_is_bored_return_wit_1 : p091_is_bored_return_wit_1.
Proof.
  unfold p091_is_bored_return_wit_1.
  intros.
  bored_pre.
  assert (i = Zlength l) by lia.
  subst i.
  entailer!.
  eapply problem_91_spec_intro; eauto.
Qed.

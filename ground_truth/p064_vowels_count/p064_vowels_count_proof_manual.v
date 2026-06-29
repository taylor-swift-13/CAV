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
From SimpleC.EE.CAV.ground_truth_p064_vowels_count Require Import p064_vowels_count_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
From AUXLib Require Import ListLib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import string_bridge.

Import naive_C_Rules.
Require Import p064_vowels_count.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p064_vowels_count.v so public contract files expose definitions only. *)

Lemma count_regular_vowels_upto_0 : forall l,
  count_regular_vowels_upto 0 l = 0.
Proof.
  intros l.
  unfold count_regular_vowels_upto.
  reflexivity.
Qed.
Lemma count_regular_vowels_list_app : forall l1 l2,
  count_regular_vowels_list (l1 ++ l2) =
  count_regular_vowels_list l1 + count_regular_vowels_list l2.
Proof.
  induction l1 as [| x xs IH]; intros l2; simpl.
  - lia.
  - rewrite IH. lia.
Qed.
Lemma firstn_succ_snoc_64 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = List.app (firstn n l) [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.
Lemma firstn_succ_Znth_64 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  List.app (firstn (Z.to_nat i) l) [Znth i l 0].
Proof.
  intros l i H.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc_64 with (d := 0) by (rewrite Zlength_correct in H; lia).
  reflexivity.
Qed.
Lemma is_regular_vowel_true : forall x,
  x = 97 \/ x = 101 \/ x = 105 \/ x = 111 \/ x = 117 \/
  x = 65 \/ x = 69 \/ x = 73 \/ x = 79 \/ x = 85 ->
  is_regular_vowel x = true.
Proof.
  intros x Hx.
  unfold is_regular_vowel.
  destruct Hx as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
    repeat rewrite Z.eqb_refl; reflexivity.
Qed.
Lemma is_regular_vowel_false : forall x,
  x <> 97 -> x <> 101 -> x <> 105 -> x <> 111 -> x <> 117 ->
  x <> 65 -> x <> 69 -> x <> 73 -> x <> 79 -> x <> 85 ->
  is_regular_vowel x = false.
Proof.
  intros x H97 H101 H105 H111 H117 H65 H69 H73 H79 H85.
  unfold is_regular_vowel.
  repeat match goal with
  | |- context[Z.eqb ?a ?b] =>
      replace (Z.eqb a b) with false by (symmetry; apply Z.eqb_neq; lia)
  end.
  reflexivity.
Qed.
Lemma count_regular_vowels_upto_step_hit : forall i l,
  0 <= i ->
  i < Zlength l ->
  (Znth i l 0 = 97 \/ Znth i l 0 = 101 \/ Znth i l 0 = 105 \/
   Znth i l 0 = 111 \/ Znth i l 0 = 117 \/
   Znth i l 0 = 65 \/ Znth i l 0 = 69 \/ Znth i l 0 = 73 \/
   Znth i l 0 = 79 \/ Znth i l 0 = 85) ->
  count_regular_vowels_upto (i + 1) l =
  count_regular_vowels_upto i l + 1.
Proof.
  intros i l Hi Hlt Hhit.
  unfold count_regular_vowels_upto.
  rewrite firstn_succ_Znth_64 by lia.
  rewrite count_regular_vowels_list_app.
  simpl.
  rewrite is_regular_vowel_true by exact Hhit.
  simpl. lia.
Qed.
Lemma count_regular_vowels_upto_step_miss : forall i l,
  0 <= i ->
  i < Zlength l ->
  Znth i l 0 <> 97 -> Znth i l 0 <> 101 -> Znth i l 0 <> 105 ->
  Znth i l 0 <> 111 -> Znth i l 0 <> 117 ->
  Znth i l 0 <> 65 -> Znth i l 0 <> 69 -> Znth i l 0 <> 73 ->
  Znth i l 0 <> 79 -> Znth i l 0 <> 85 ->
  count_regular_vowels_upto (i + 1) l =
  count_regular_vowels_upto i l.
Proof.
  intros i l Hi Hlt H97 H101 H105 H111 H117 H65 H69 H73 H79 H85.
  unfold count_regular_vowels_upto.
  rewrite firstn_succ_Znth_64 by lia.
  rewrite count_regular_vowels_list_app.
  simpl.
  rewrite is_regular_vowel_false by auto.
  simpl. lia.
Qed.
Lemma last_y_add_zero : forall l,
  Zlength l = 0 ->
  last_y_add l = 0.
Proof.
  intros l Hlen.
  unfold last_y_add.
  rewrite Hlen, Z.eqb_refl.
  reflexivity.
Qed.
Lemma last_y_add_hit : forall l n,
  Zlength l = n ->
  n > 0 ->
  (Znth (n - 1) l 0 = 121 \/ Znth (n - 1) l 0 = 89) ->
  last_y_add l = 1.
Proof.
  intros l n Hlen Hpos Hy.
  unfold last_y_add.
  rewrite Hlen.
  replace (Z.eqb n 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold is_y.
  destruct Hy as [Hy | Hy]; rewrite Hy.
  - rewrite Z.eqb_refl. reflexivity.
  - replace (Z.eqb 89 121) with false by reflexivity.
    rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma last_y_add_miss : forall l n,
  Zlength l = n ->
  n > 0 ->
  Znth (n - 1) l 0 <> 121 ->
  Znth (n - 1) l 0 <> 89 ->
  last_y_add l = 0.
Proof.
  intros l n Hlen Hpos H121 H89.
  unfold last_y_add.
  rewrite Hlen.
  replace (Z.eqb n 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold is_y.
  replace (Z.eqb (Znth (n - 1) l 0) 121) with false by
    (symmetry; apply Z.eqb_neq; lia).
  replace (Z.eqb (Znth (n - 1) l 0) 89) with false by
    (symmetry; apply Z.eqb_neq; lia).
  reflexivity.
Qed.
Lemma problem_64_spec_intro : forall s output,
  output = count_regular_vowels_upto (Zlength s) s + last_y_add s ->
  problem_64_spec s output.
Proof.
  intros s output Hout.
  unfold problem_64_spec, count_regular_vowels_upto in *.
  assert (Hn : Z.to_nat (Zlength s) = length s) by (rewrite Zlength_correct; lia).
  rewrite Hn in Hout.
  rewrite firstn_all in Hout.
  exact Hout.
Qed.


Ltac solve_vowel_hit :=
  pre_process;
  repeat match goal with
  | H : ?x = count_regular_vowels_upto ?i ?l |- _ => subst x
  end;
  repeat rewrite app_Znth1 in * by lia;
  match goal with
  | i : Z, l : list Z |- _ =>
      assert (Hhit:
        Znth i l 0 = 97 \/ Znth i l 0 = 101 \/ Znth i l 0 = 105 \/
        Znth i l 0 = 111 \/ Znth i l 0 = 117 \/
        Znth i l 0 = 65 \/ Znth i l 0 = 69 \/ Znth i l 0 = 73 \/
        Znth i l 0 = 79 \/ Znth i l 0 = 85) by lia;
      rewrite count_regular_vowels_upto_step_hit by (lia || exact Hhit)
  end;
  entailer!.

Lemma proof_of_p064_vowels_count_entail_wit_1 : p064_vowels_count_entail_wit_1.
Proof.
  unfold p064_vowels_count_entail_wit_1.
  intros.
  pre_process.
  subst retval.
  rewrite count_regular_vowels_upto_0.
  entailer!.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_1 : p064_vowels_count_entail_wit_2_1.
Proof.
  unfold p064_vowels_count_entail_wit_2_1.
  intros.
  solve_vowel_hit.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_2 : p064_vowels_count_entail_wit_2_2.
Proof.
  unfold p064_vowels_count_entail_wit_2_2.
  intros.
  solve_vowel_hit.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_3 : p064_vowels_count_entail_wit_2_3.
Proof.
  unfold p064_vowels_count_entail_wit_2_3.
  intros.
  solve_vowel_hit.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_4 : p064_vowels_count_entail_wit_2_4.
Proof.
  unfold p064_vowels_count_entail_wit_2_4.
  intros.
  solve_vowel_hit.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_5 : p064_vowels_count_entail_wit_2_5.
Proof.
  unfold p064_vowels_count_entail_wit_2_5.
  intros.
  solve_vowel_hit.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_6 : p064_vowels_count_entail_wit_2_6.
Proof.
  unfold p064_vowels_count_entail_wit_2_6.
  intros.
  solve_vowel_hit.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_7 : p064_vowels_count_entail_wit_2_7.
Proof.
  unfold p064_vowels_count_entail_wit_2_7.
  intros.
  solve_vowel_hit.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_8 : p064_vowels_count_entail_wit_2_8.
Proof.
  unfold p064_vowels_count_entail_wit_2_8.
  intros.
  solve_vowel_hit.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_9 : p064_vowels_count_entail_wit_2_9.
Proof.
  unfold p064_vowels_count_entail_wit_2_9.
  intros.
  solve_vowel_hit.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_10 : p064_vowels_count_entail_wit_2_10.
Proof.
  unfold p064_vowels_count_entail_wit_2_10.
  intros.
  solve_vowel_hit.
Qed.

Lemma proof_of_p064_vowels_count_entail_wit_2_11 : p064_vowels_count_entail_wit_2_11.
Proof.
  unfold p064_vowels_count_entail_wit_2_11.
  intros.
  pre_process.
  repeat match goal with
  | H : ?x = count_regular_vowels_upto ?i ?l |- _ => subst x
  end.
  repeat rewrite app_Znth1 in * by lia.
  rewrite count_regular_vowels_upto_step_miss by lia.
  entailer!.
Qed.

Lemma proof_of_p064_vowels_count_return_wit_1 : p064_vowels_count_return_wit_1.
Proof.
  unfold p064_vowels_count_return_wit_1.
  intros.
  pre_process.
  repeat match goal with
  | H : ?x = count_regular_vowels_upto ?i ?l |- _ => subst x
  end.
  assert (i = len) by lia.
  subst i.
  repeat rewrite app_Znth1 in * by lia.
  entailer!.
  eapply problem_64_spec_intro; eauto.
  match goal with
  | Hlen : Zlength l = len |- _ => rewrite Hlen
  end.
  rewrite last_y_add_hit with (n := len) by (auto; lia).
  lia.
Qed.

Lemma proof_of_p064_vowels_count_return_wit_2 : p064_vowels_count_return_wit_2.
Proof.
  unfold p064_vowels_count_return_wit_2.
  intros.
  pre_process.
  repeat match goal with
  | H : ?x = count_regular_vowels_upto ?i ?l |- _ => subst x
  end.
  assert (i = len) by lia.
  subst i.
  repeat rewrite app_Znth1 in * by lia.
  entailer!.
  eapply problem_64_spec_intro; eauto.
  match goal with
  | Hlen : Zlength l = len |- _ => rewrite Hlen
  end.
  rewrite last_y_add_hit with (n := len) by (auto; lia).
  lia.
Qed.

Lemma proof_of_p064_vowels_count_return_wit_3 : p064_vowels_count_return_wit_3.
Proof.
  unfold p064_vowels_count_return_wit_3.
  intros.
  pre_process.
  repeat match goal with
  | H : ?x = count_regular_vowels_upto ?i ?l |- _ => subst x
  end.
  assert (i = len) by lia.
  subst i.
  entailer!.
  eapply problem_64_spec_intro; eauto.
  match goal with
  | Hlen : Zlength l = len |- _ => rewrite Hlen
  end.
  rewrite last_y_add_zero by lia.
  lia.
Qed.

Lemma proof_of_p064_vowels_count_return_wit_4 : p064_vowels_count_return_wit_4.
Proof.
  unfold p064_vowels_count_return_wit_4.
  intros.
  pre_process.
  repeat match goal with
  | H : ?x = count_regular_vowels_upto ?i ?l |- _ => subst x
  end.
  assert (i = len) by lia.
  subst i.
  repeat rewrite app_Znth1 in * by lia.
  entailer!.
  eapply problem_64_spec_intro; eauto.
  match goal with
  | Hlen : Zlength l = len |- _ => rewrite Hlen
  end.
  rewrite last_y_add_miss with (n := len) by (auto; lia).
  lia.
Qed.

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
From SimpleC.EE.CAV.ground_truth_p078_hex_key Require Import p078_hex_key_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
From AUXLib Require Import ListLib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import string_bridge.

Import naive_C_Rules.
Require Import p078_hex_key.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p078_hex_key.v so public contract files expose definitions only. *)

Lemma count_prime_hex_upto_0 : forall l,
  count_prime_hex_upto 0 l = 0.
Proof.
  intros l.
  unfold count_prime_hex_upto.
  reflexivity.
Qed.
Lemma count_prime_hex_list_app : forall l1 l2,
  count_prime_hex_list (l1 ++ l2) =
  count_prime_hex_list l1 + count_prime_hex_list l2.
Proof.
  induction l1 as [| x xs IH]; intros l2; simpl.
  - lia.
  - rewrite IH. lia.
Qed.
Lemma count_prime_hex_list_nonneg : forall l,
  0 <= count_prime_hex_list l.
Proof.
  induction l as [| x xs IH]; simpl.
  - lia.
  - destruct (is_prime_hex x); lia.
Qed.
Lemma firstn_succ_snoc_78 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = List.app (firstn n l) [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.
Lemma firstn_succ_Znth_78 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  List.app (firstn (Z.to_nat i) l) [Znth i l 0].
Proof.
  intros l i H.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc_78 with (d := 0) by (rewrite Zlength_correct in H; lia).
  reflexivity.
Qed.
Lemma is_prime_hex_true : forall x,
  x = 50 \/ x = 51 \/ x = 53 \/ x = 55 \/ x = 66 \/ x = 68 ->
  is_prime_hex x = true.
Proof.
  intros x Hx.
  unfold is_prime_hex.
  destruct Hx as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    repeat rewrite Z.eqb_refl; reflexivity.
Qed.
Lemma is_prime_hex_false : forall x,
  x <> 50 -> x <> 51 -> x <> 53 -> x <> 55 -> x <> 66 -> x <> 68 ->
  is_prime_hex x = false.
Proof.
  intros x H50 H51 H53 H55 H66 H68.
  unfold is_prime_hex.
  repeat match goal with
  | |- context[Z.eqb ?a ?b] =>
      replace (Z.eqb a b) with false by (symmetry; apply Z.eqb_neq; lia)
  end.
  reflexivity.
Qed.
Lemma count_prime_hex_upto_step_hit : forall i l,
  0 <= i ->
  i < Zlength l ->
  (Znth i l 0 = 50 \/ Znth i l 0 = 51 \/ Znth i l 0 = 53 \/
   Znth i l 0 = 55 \/ Znth i l 0 = 66 \/ Znth i l 0 = 68) ->
  count_prime_hex_upto (i + 1) l =
  count_prime_hex_upto i l + 1.
Proof.
  intros i l Hi Hlt Hhit.
  unfold count_prime_hex_upto.
  rewrite firstn_succ_Znth_78 by lia.
  rewrite count_prime_hex_list_app.
  simpl.
  rewrite is_prime_hex_true by exact Hhit.
  simpl. lia.
Qed.
Lemma count_prime_hex_upto_step_miss : forall i l,
  0 <= i ->
  i < Zlength l ->
  Znth i l 0 <> 50 ->
  Znth i l 0 <> 51 ->
  Znth i l 0 <> 53 ->
  Znth i l 0 <> 55 ->
  Znth i l 0 <> 66 ->
  Znth i l 0 <> 68 ->
  count_prime_hex_upto (i + 1) l =
  count_prime_hex_upto i l.
Proof.
  intros i l Hi Hlt H50 H51 H53 H55 H66 H68.
  unfold count_prime_hex_upto.
  rewrite firstn_succ_Znth_78 by lia.
  rewrite count_prime_hex_list_app.
  simpl.
  rewrite is_prime_hex_false by auto.
  simpl. lia.
Qed.
Lemma problem_78_spec_intro : forall s output,
  ascii_range s ->
  output = count_prime_hex_upto (Zlength s) s ->
  problem_78_spec s output.
Proof.
  intros s output _ Hout.
  unfold problem_78_spec, count_prime_hex_upto in *.
  rewrite Hout.
  replace (Z.to_nat (Zlength s)) with (length s) by (rewrite Zlength_correct; lia).
  rewrite firstn_all.
  reflexivity.
Qed.


Ltac solve_hex_hit :=
  pre_process;
  repeat match goal with
  | H : ?x = count_prime_hex_upto ?i ?l |- _ => subst x
  end;
  repeat rewrite app_Znth1 in * by lia;
  match goal with
  | i : Z, l : list Z |- _ =>
      assert (Hhit:
        Znth i l 0 = 50 \/ Znth i l 0 = 51 \/ Znth i l 0 = 53 \/
        Znth i l 0 = 55 \/ Znth i l 0 = 66 \/ Znth i l 0 = 68) by lia;
      rewrite count_prime_hex_upto_step_hit by (lia || exact Hhit)
  end;
  entailer!.

Lemma proof_of_p078_hex_key_entail_wit_1 : p078_hex_key_entail_wit_1.
Proof.
  unfold p078_hex_key_entail_wit_1.
  intros.
  pre_process.
  subst retval.
  rewrite count_prime_hex_upto_0.
  entailer!.
Qed.

Lemma proof_of_p078_hex_key_entail_wit_2_1 : p078_hex_key_entail_wit_2_1.
Proof.
  unfold p078_hex_key_entail_wit_2_1.
  intros.
  solve_hex_hit.
Qed.

Lemma proof_of_p078_hex_key_entail_wit_2_2 : p078_hex_key_entail_wit_2_2.
Proof.
  unfold p078_hex_key_entail_wit_2_2.
  intros.
  solve_hex_hit.
Qed.

Lemma proof_of_p078_hex_key_entail_wit_2_3 : p078_hex_key_entail_wit_2_3.
Proof.
  unfold p078_hex_key_entail_wit_2_3.
  intros.
  solve_hex_hit.
Qed.

Lemma proof_of_p078_hex_key_entail_wit_2_4 : p078_hex_key_entail_wit_2_4.
Proof.
  unfold p078_hex_key_entail_wit_2_4.
  intros.
  solve_hex_hit.
Qed.

Lemma proof_of_p078_hex_key_entail_wit_2_5 : p078_hex_key_entail_wit_2_5.
Proof.
  unfold p078_hex_key_entail_wit_2_5.
  intros.
  solve_hex_hit.
Qed.

Lemma proof_of_p078_hex_key_entail_wit_2_6 : p078_hex_key_entail_wit_2_6.
Proof.
  unfold p078_hex_key_entail_wit_2_6.
  intros.
  solve_hex_hit.
Qed.

Lemma proof_of_p078_hex_key_entail_wit_2_7 : p078_hex_key_entail_wit_2_7.
Proof.
  unfold p078_hex_key_entail_wit_2_7.
  intros.
  pre_process.
  repeat match goal with
  | H : ?x = count_prime_hex_upto ?i ?l |- _ => subst x
  end.
  repeat rewrite app_Znth1 in * by lia.
  rewrite count_prime_hex_upto_step_miss by lia.
  entailer!.
Qed.

Lemma proof_of_p078_hex_key_return_wit_1 : p078_hex_key_return_wit_1.
Proof.
  unfold p078_hex_key_return_wit_1.
  intros.
  pre_process.
  repeat match goal with
  | H : ?x = count_prime_hex_upto ?i ?l |- _ => subst x
  end.
  assert (i = len) by lia.
  subst i.
  entailer!.
  eapply problem_78_spec_intro; eauto.
  rewrite H2.
  reflexivity.
Qed.

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
From SimpleC.EE.CAV.ground_truth_p098_count_upper Require Import p098_count_upper_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
From AUXLib Require Import ListLib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import string_bridge.

Import naive_C_Rules.
Require Import p098_count_upper.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p098_count_upper.v so public contract files expose definitions only. *)

Lemma count_upper_even_upto_0 : forall l,
  count_upper_even_upto 0 l = 0.
Proof.
  intros l.
  unfold count_upper_even_upto.
  reflexivity.
Qed.
Lemma is_upper_vowel_true : forall x,
  x = 65 \/ x = 69 \/ x = 73 \/ x = 79 \/ x = 85 ->
  is_upper_vowel x = true.
Proof.
  intros x Hx.
  unfold is_upper_vowel.
  destruct Hx as [-> | [-> | [-> | [-> | ->]]]];
    repeat rewrite Z.eqb_refl; reflexivity.
Qed.
Lemma is_upper_vowel_false : forall x,
  x <> 65 -> x <> 69 -> x <> 73 -> x <> 79 -> x <> 85 ->
  is_upper_vowel x = false.
Proof.
  intros x H65 H69 H73 H79 H85.
  unfold is_upper_vowel.
  repeat match goal with
  | |- context[Z.eqb ?a ?b] =>
      replace (Z.eqb a b) with false by (symmetry; apply Z.eqb_neq; lia)
  end.
  reflexivity.
Qed.
Lemma is_even_index_true : forall i,
  Z.rem i 2 = 0 ->
  is_even_index i = true.
Proof.
  intros i Hi.
  unfold is_even_index.
  rewrite Hi, Z.eqb_refl.
  reflexivity.
Qed.
Lemma is_even_index_false : forall i,
  Z.rem i 2 <> 0 ->
  is_even_index i = false.
Proof.
  intros i Hi.
  unfold is_even_index.
  apply Z.eqb_neq.
  exact Hi.
Qed.
Lemma count_upper_even_upto_step_hit : forall i l,
  0 <= i ->
  Z.rem i 2 = 0 ->
  (Znth i l 0 = 65 \/ Znth i l 0 = 69 \/ Znth i l 0 = 73 \/
   Znth i l 0 = 79 \/ Znth i l 0 = 85) ->
  count_upper_even_upto (i + 1) l =
  count_upper_even_upto i l + 1.
Proof.
  intros i l Hi Heven Hhit.
  unfold count_upper_even_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  rewrite is_even_index_true by exact Heven.
  rewrite is_upper_vowel_true by exact Hhit.
  reflexivity.
Qed.
Lemma count_upper_even_upto_step_even_miss : forall i l,
  0 <= i ->
  Z.rem i 2 = 0 ->
  Znth i l 0 <> 65 -> Znth i l 0 <> 69 -> Znth i l 0 <> 73 ->
  Znth i l 0 <> 79 -> Znth i l 0 <> 85 ->
  count_upper_even_upto (i + 1) l =
  count_upper_even_upto i l.
Proof.
  intros i l Hi Heven H65 H69 H73 H79 H85.
  unfold count_upper_even_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  rewrite is_even_index_true by exact Heven.
  rewrite is_upper_vowel_false by auto.
  reflexivity.
Qed.
Lemma count_upper_even_upto_step_odd : forall i l,
  0 <= i ->
  Z.rem i 2 <> 0 ->
  count_upper_even_upto (i + 1) l =
  count_upper_even_upto i l.
Proof.
  intros i l Hi Hodd.
  unfold count_upper_even_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  rewrite is_even_index_false by exact Hodd.
  reflexivity.
Qed.
Lemma count_upper_even_upto_nat_app_unchanged : forall n l x,
  (n <= length l)%nat ->
  count_upper_even_upto_nat n (l ++ [x]) =
  count_upper_even_upto_nat n l.
Proof.
  induction n as [| n IH]; intros l x Hn.
  - reflexivity.
  - simpl.
    rewrite IH by lia.
    rewrite app_Znth1 by (rewrite Zlength_correct; lia).
    reflexivity.
Qed.
Lemma count_upper_even_upto_Zlength_app_single : forall l x,
  count_upper_even_upto (Zlength (l ++ [x])) (l ++ [x]) =
  count_upper_even_upto (Zlength l) l +
  (if andb (is_even_index (Zlength l)) (is_upper_vowel x) then 1 else 0).
Proof.
  intros l x.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  unfold count_upper_even_upto.
  replace (Zlength l + Z.succ 0) with (Z.of_nat (S (length l)))
    by (rewrite Zlength_correct; lia).
  rewrite Nat2Z.id.
  replace (Z.to_nat (Zlength l)) with (length l)
    by (rewrite Zlength_correct; lia).
  simpl.
  replace (Z.of_nat (length l)) with (Zlength l)
    by (rewrite Zlength_correct; lia).
  rewrite (count_upper_even_upto_nat_app_unchanged (length l) l x)
    by apply Nat.le_refl.
  rewrite app_Znth2 by lia.
  replace (Zlength l - Zlength l) with 0 by lia.
  simpl.
  change (Znth 0 [x] 0) with x.
  destruct (andb (is_even_index (Zlength l)) (is_upper_vowel x)).
  - reflexivity.
  - rewrite Z.add_0_r. reflexivity.
Qed.
Lemma count_upper_even_from_app_single : forall i l x,
  count_upper_even_from i (l ++ [x]) =
  count_upper_even_from i l +
  (if andb (is_even_index (i + Zlength l)) (is_upper_vowel x) then 1 else 0).
Proof.
  intros i l.
  revert i.
  induction l as [| a l IH]; intros i x.
  - simpl. rewrite Zlength_nil. replace (i + 0) with i by lia.
    rewrite Z.add_0_r. reflexivity.
  - simpl.
    rewrite (IH (i + 1) x).
    rewrite Zlength_cons.
    replace (i + Z.succ (Zlength l)) with (i + 1 + Zlength l) by lia.
    remember (andb (is_even_index (i + 1 + Zlength l)) (is_upper_vowel x)) as b.
    destruct b; lia.
Qed.
Lemma count_upper_even_upto_Zlength_eq_from : forall l,
  count_upper_even_upto (Zlength l) l =
  count_upper_even_from 0 l.
Proof.
  induction l using rev_ind.
  - reflexivity.
  - rewrite count_upper_even_upto_Zlength_app_single.
    rewrite count_upper_even_from_app_single.
    rewrite IHl.
    replace (0 + Zlength l) with (Zlength l) by lia.
    reflexivity.
Qed.
Lemma problem_98_spec_intro : forall s output,
  output = count_upper_even_upto (Zlength s) s ->
  problem_98_spec s output.
Proof.
  intros s output Hout.
  unfold problem_98_spec.
  rewrite Hout.
  apply count_upper_even_upto_Zlength_eq_from.
Qed.


Ltac solve_upper_hit :=
  pre_process;
  repeat match goal with
  | H : ?x = count_upper_even_upto ?i ?l |- _ => subst x
  end;
  match goal with
  | |- context[count_upper_even_upto (?i + 1) ?l] =>
      repeat rewrite app_Znth1 in * by lia;
      assert (Hhit:
        Znth i l 0 = 65 \/ Znth i l 0 = 69 \/ Znth i l 0 = 73 \/
        Znth i l 0 = 79 \/ Znth i l 0 = 85) by lia;
      rewrite count_upper_even_upto_step_hit with (i := i) (l := l)
        by (try lia; try assumption; exact Hhit)
  end;
  entailer!.

Lemma proof_of_p098_count_upper_entail_wit_1 : p098_count_upper_entail_wit_1.
Proof.
  unfold p098_count_upper_entail_wit_1.
  intros.
  pre_process.
  subst retval.
  rewrite count_upper_even_upto_0.
  entailer!.
Qed.

Lemma proof_of_p098_count_upper_entail_wit_2_1 : p098_count_upper_entail_wit_2_1.
Proof.
  unfold p098_count_upper_entail_wit_2_1.
  intros.
  solve_upper_hit.
Qed.

Lemma proof_of_p098_count_upper_entail_wit_2_2 : p098_count_upper_entail_wit_2_2.
Proof.
  unfold p098_count_upper_entail_wit_2_2.
  intros.
  solve_upper_hit.
Qed.

Lemma proof_of_p098_count_upper_entail_wit_2_3 : p098_count_upper_entail_wit_2_3.
Proof.
  unfold p098_count_upper_entail_wit_2_3.
  intros.
  solve_upper_hit.
Qed.

Lemma proof_of_p098_count_upper_entail_wit_2_4 : p098_count_upper_entail_wit_2_4.
Proof.
  unfold p098_count_upper_entail_wit_2_4.
  intros.
  solve_upper_hit.
Qed.

Lemma proof_of_p098_count_upper_entail_wit_2_5 : p098_count_upper_entail_wit_2_5.
Proof.
  unfold p098_count_upper_entail_wit_2_5.
  intros.
  solve_upper_hit.
Qed.

Lemma proof_of_p098_count_upper_entail_wit_2_6 : p098_count_upper_entail_wit_2_6.
Proof.
  unfold p098_count_upper_entail_wit_2_6.
  intros.
  pre_process.
  repeat match goal with
  | H : ?x = count_upper_even_upto ?i ?l |- _ => subst x
  end.
  repeat rewrite app_Znth1 in * by lia.
  rewrite count_upper_even_upto_step_even_miss by lia.
  entailer!.
Qed.

Lemma proof_of_p098_count_upper_entail_wit_2_7 : p098_count_upper_entail_wit_2_7.
Proof.
  unfold p098_count_upper_entail_wit_2_7.
  intros.
  pre_process.
  repeat match goal with
  | H : ?x = count_upper_even_upto ?i ?l |- _ => subst x
  end.
  rewrite count_upper_even_upto_step_odd by lia.
  entailer!.
Qed.

Lemma proof_of_p098_count_upper_return_wit_1 : p098_count_upper_return_wit_1.
Proof.
  unfold p098_count_upper_return_wit_1.
  intros.
  pre_process.
  repeat match goal with
  | H : ?x = count_upper_even_upto ?i ?l |- _ => subst x
  end.
  assert (i = len) by lia.
  subst i.
  entailer!.
  apply problem_98_spec_intro.
  match goal with
  | Hlen : Zlength l = len |- _ => rewrite Hlen
  end.
  reflexivity.
Qed.

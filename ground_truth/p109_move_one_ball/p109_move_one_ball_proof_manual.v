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
From SimpleC.EE.CAV.ground_truth_p109_move_one_ball Require Import p109_move_one_ball_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import List ZArith Arith.
Require Import Coq.Sorting.Sorted.

Import naive_C_Rules.
Require Import p109_move_one_ball.
Local Open Scope sac.
Require Import Coq.micromega.Lia.

Local Open Scope list_scope.

(* Proof helpers moved from p109_move_one_ball.v so public contract files expose definitions only. *)

Lemma count_descents_prefix_1 : forall arr,
  count_descents_prefix 1 arr = 0.
Proof.
  reflexivity.
Qed.
Lemma count_descents_prefix_step_lt : forall arr i,
  1 <= i ->
  Znth i arr 0 < Znth (i - 1) arr 0 ->
  count_descents_prefix (i + 1) arr =
    count_descents_prefix i arr + 1.
Proof.
  intros arr i Hi Hlt.
  unfold count_descents_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  destruct (Z.to_nat i) as [|n] eqn:Hi_nat; [lia |].
  simpl.
  change (Z.pos (Pos.of_succ_nat n)) with (Z.of_nat (S n)).
  change match Pos.of_succ_nat n with
         | (p~1)%positive => Z.pos p~0
         | (p~0)%positive => Z.pos (Pos.pred_double p)
         | 1%positive => 0
         end with (Z.of_nat (S n) - 1).
  replace (Z.of_nat (S n)) with i by lia.
  apply Z.ltb_lt in Hlt.
  rewrite Hlt.
  reflexivity.
Qed.
Lemma count_descents_prefix_step_ge : forall arr i,
  1 <= i ->
  Znth i arr 0 >= Znth (i - 1) arr 0 ->
  count_descents_prefix (i + 1) arr =
    count_descents_prefix i arr.
Proof.
  intros arr i Hi Hge.
  unfold count_descents_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  destruct (Z.to_nat i) as [|n] eqn:Hi_nat; [lia |].
  simpl.
  change (Z.pos (Pos.of_succ_nat n)) with (Z.of_nat (S n)).
  change match Pos.of_succ_nat n with
         | (p~1)%positive => Z.pos p~0
         | (p~0)%positive => Z.pos (Pos.pred_double p)
         | 1%positive => 0
         end with (Z.of_nat (S n) - 1).
  replace (Z.of_nat (S n)) with i by lia.
  assert ((Znth i arr 0 <? Znth (i - 1) arr 0) = false) as Hfalse.
  { apply Z.ltb_ge. lia. }
  rewrite Hfalse.
  lia.
Qed.
Lemma cyclic_descents_tail_gt : forall arr,
  1 <= Zlength arr ->
  Znth (Zlength arr - 1) arr 0 > Znth 0 arr 0 ->
  cyclic_descents arr =
    count_descents_prefix (Zlength arr) arr + 1.
Proof.
  intros arr Hlen Hgt.
  unfold cyclic_descents.
  assert ((Znth 0 arr 0 <? Znth (Zlength arr - 1) arr 0) = true) as Htrue.
  { apply Z.ltb_lt. lia. }
  rewrite Htrue.
  reflexivity.
Qed.
Lemma cyclic_descents_tail_le : forall arr,
  1 <= Zlength arr ->
  Znth (Zlength arr - 1) arr 0 <= Znth 0 arr 0 ->
  cyclic_descents arr =
    count_descents_prefix (Zlength arr) arr.
Proof.
  intros arr Hlen Hle.
  unfold cyclic_descents.
  assert ((Znth 0 arr 0 <? Znth (Zlength arr - 1) arr 0) = false) as Hfalse.
  { apply Z.ltb_ge. lia. }
  rewrite Hfalse.
  lia.
Qed.
Lemma problem_109_spec_of_cyclic_true : forall arr,
  descents_int_range arr ->
  cyclic_descents arr < 2 ->
  problem_109_spec arr 1.
Proof.
  intros arr _ Hcyc.
  unfold problem_109_spec.
  left.
  lia.
Qed.
Lemma problem_109_spec_of_cyclic_false : forall arr,
  descents_int_range arr ->
  cyclic_descents arr >= 2 ->
  problem_109_spec arr 0.
Proof.
  intros arr _ Hcyc.
  unfold problem_109_spec.
  right.
  lia.
Qed.


Lemma proof_of_p109_move_one_ball_safety_wit_5 : p109_move_one_ball_safety_wit_5.
Proof.
  pre_process.
  subst num.
  match goal with
  | H: descents_int_range input_l |- _ =>
      destruct H as [Hrange _];
      pose proof (Hrange i ltac:(lia)) as Hsafe
  end.
  entailer!.
Qed. 

Lemma proof_of_p109_move_one_ball_safety_wit_12 : p109_move_one_ball_safety_wit_12.
Proof.
  pre_process.
  assert (Hi : i = arr_size_pre) by lia.
  subst i num.
  match goal with
  | H: descents_int_range input_l |- _ =>
      destruct H as [_ Hrange]
  end.
  assert (Hgt : Znth (Zlength input_l - 1) input_l 0 > Znth 0 input_l 0).
  { replace (Zlength input_l) with arr_size_pre by lia; lia. }
  rewrite (cyclic_descents_tail_gt input_l ltac:(lia) Hgt) in Hrange.
  replace arr_size_pre with (Zlength input_l) by lia.
  entailer!.
Qed. 

Lemma proof_of_p109_move_one_ball_entail_wit_1 : p109_move_one_ball_entail_wit_1.
Proof.
  pre_process.
Qed. 

Lemma proof_of_p109_move_one_ball_entail_wit_2_1 : p109_move_one_ball_entail_wit_2_1.
Proof.
  pre_process.
  subst num.
  rewrite count_descents_prefix_step_lt by lia.
  entailer!.
Qed. 

Lemma proof_of_p109_move_one_ball_entail_wit_2_2 : p109_move_one_ball_entail_wit_2_2.
Proof.
  pre_process.
  subst num.
  rewrite count_descents_prefix_step_ge by lia.
  entailer!.
Qed. 

Lemma proof_of_p109_move_one_ball_return_wit_1 : p109_move_one_ball_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = arr_size_pre) by lia.
  subst i num.
  entailer!.
  assert (Hle : Znth (Zlength input_l - 1) input_l 0 <= Znth 0 input_l 0).
  { replace (Zlength input_l) with arr_size_pre by lia; lia. }
  apply problem_109_spec_of_cyclic_false.
  - exact H6.
  - rewrite cyclic_descents_tail_le by lia.
    replace (Zlength input_l) with arr_size_pre by lia.
    lia.
Qed. 

Lemma proof_of_p109_move_one_ball_return_wit_2 : p109_move_one_ball_return_wit_2.
Proof.
  pre_process.
  assert (Hi : i = arr_size_pre) by lia.
  subst i num.
  entailer!.
  assert (Hgt : Znth (Zlength input_l - 1) input_l 0 > Znth 0 input_l 0).
  { replace (Zlength input_l) with arr_size_pre by lia; lia. }
  apply problem_109_spec_of_cyclic_false.
  - exact H6.
  - rewrite cyclic_descents_tail_gt by lia.
    replace (Zlength input_l) with arr_size_pre by lia.
    lia.
Qed. 

Lemma proof_of_p109_move_one_ball_return_wit_3 : p109_move_one_ball_return_wit_3.
Proof.
  pre_process.
  assert (Hi : i = arr_size_pre) by lia.
  subst i num.
  entailer!.
  assert (Hle : Znth (Zlength input_l - 1) input_l 0 <= Znth 0 input_l 0).
  { replace (Zlength input_l) with arr_size_pre by lia; lia. }
  apply problem_109_spec_of_cyclic_true.
  - exact H6.
  - rewrite cyclic_descents_tail_le by lia.
    replace (Zlength input_l) with arr_size_pre by lia.
    lia.
Qed. 

Lemma proof_of_p109_move_one_ball_return_wit_4 : p109_move_one_ball_return_wit_4.
Proof.
  pre_process.
  assert (Hi : i = arr_size_pre) by lia.
  subst i num.
  entailer!.
  assert (Hgt : Znth (Zlength input_l - 1) input_l 0 > Znth 0 input_l 0).
  { replace (Zlength input_l) with arr_size_pre by lia; lia. }
  apply problem_109_spec_of_cyclic_true.
  - exact H6.
  - rewrite cyclic_descents_tail_gt by lia.
    replace (Zlength input_l) with arr_size_pre by lia.
    lia.
Qed. 

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
From SimpleC.EE.CAV.ground_truth_p122_add_elements Require Import p122_add_elements_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p122_add_elements.
Local Open Scope sac.
Require Import Lia.

Local Open Scope list_scope.

(* Proof helpers moved from p122_add_elements.v so public contract files expose definitions only. *)

Lemma sum_two_digit_upto_0 : forall l,
  sum_two_digit_upto 0 l = 0.
Proof.
  intros l.
  unfold sum_two_digit_upto.
  reflexivity.
Qed.
Lemma sum_two_digit_upto_step_in : forall i l,
  0 <= i ->
  -99 <= Znth i l 0 ->
  Znth i l 0 <= 99 ->
  sum_two_digit_upto (i + 1) l =
  sum_two_digit_upto i l + Znth i l 0.
Proof.
  intros i l Hi Hlo Hhi.
  unfold sum_two_digit_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  assert (Z.leb (-99) (Znth i l 0) = true) as Hleb_lo by (apply Z.leb_le; lia).
  assert (Z.leb (Znth i l 0) 99 = true) as Hleb_hi by (apply Z.leb_le; lia).
  rewrite Hleb_lo, Hleb_hi.
  reflexivity.
Qed.
Lemma sum_two_digit_upto_step_hi : forall i l,
  0 <= i ->
  Znth i l 0 > 99 ->
  sum_two_digit_upto (i + 1) l =
  sum_two_digit_upto i l.
Proof.
  intros i l Hi Hhi.
  unfold sum_two_digit_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  assert (Z.leb (Znth i l 0) 99 = false) as Hleb_hi by (apply Z.leb_gt; lia).
  rewrite Hleb_hi.
  destruct (Z.leb (-99) (Znth i l 0)); reflexivity.
Qed.
Lemma sum_two_digit_upto_step_lo : forall i l,
  0 <= i ->
  Znth i l 0 < -99 ->
  sum_two_digit_upto (i + 1) l =
  sum_two_digit_upto i l.
Proof.
  intros i l Hi Hlo.
  unfold sum_two_digit_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  assert (Z.leb (-99) (Znth i l 0) = false) as Hleb_lo by (apply Z.leb_gt; lia).
  rewrite Hleb_lo.
  reflexivity.
Qed.
Lemma two_digit_bool_equiv_122 : forall x,
  andb (Z.leb (-99) x) (Z.leb x 99) = is_at_most_two_digits x.
Proof.
  intros x.
  unfold is_at_most_two_digits.
  destruct (andb (Z.leb (-99) x) (Z.leb x 99)) eqn:Hold;
    destruct (andb (Z.ltb (-100) x) (Z.ltb x 100)) eqn:Hnew; auto; exfalso.
  - apply andb_prop in Hold as [Hlo Hhi].
    apply Z.leb_le in Hlo.
    apply Z.leb_le in Hhi.
    apply Bool.andb_false_iff in Hnew.
    destruct Hnew as [Hnew | Hnew].
    + apply Z.ltb_ge in Hnew. lia.
    + apply Z.ltb_ge in Hnew. lia.
  - apply andb_prop in Hnew as [Hlo Hhi].
    apply Z.ltb_lt in Hlo.
    apply Z.ltb_lt in Hhi.
    apply Bool.andb_false_iff in Hold.
    destruct Hold as [Hold | Hold].
    + apply Z.leb_gt in Hold. lia.
    + apply Z.leb_gt in Hold. lia.
Qed.
Lemma firstn_snoc_nth_122 : forall {A : Type} n (l : list A) d,
  (n < length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  induction n; intros l d Hn.
  - destruct l as [|x xs]; simpl in *; [lia | reflexivity].
  - destruct l as [|x xs]; simpl in *; [lia |].
    rewrite (IHn xs d) by lia.
    reflexivity.
Qed.
Lemma fold_left_filter_snoc_122 : forall l x,
  fold_left Z.add (filter is_at_most_two_digits (l ++ [x])) 0 =
  fold_left Z.add (filter is_at_most_two_digits l) 0 +
  (if is_at_most_two_digits x then x else 0).
Proof.
  intros l x.
  rewrite filter_app.
  rewrite fold_left_app.
  simpl.
  destruct (is_at_most_two_digits x); simpl; lia.
Qed.
Lemma Znth_of_nat_nth_122 : forall (l : list Z) n d,
  Znth (Z.of_nat n) l d = nth n l d.
Proof.
  intros l n d.
  unfold Znth.
  rewrite Nat2Z.id.
  reflexivity.
Qed.
Lemma sum_two_digit_upto_nat_correct_122 : forall n l,
  (n <= length l)%nat ->
  sum_two_digit_upto_nat n l =
  fold_left Z.add (filter is_at_most_two_digits (firstn n l)) 0.
Proof.
  induction n; intros l Hn.
  - reflexivity.
  - assert (Hlt : (n < length l)%nat) by lia.
    cbn [sum_two_digit_upto_nat].
    rewrite IHn by lia.
    rewrite (firstn_snoc_nth_122 n l 0 Hlt).
    rewrite fold_left_filter_snoc_122.
    rewrite Znth_of_nat_nth_122.
    rewrite two_digit_bool_equiv_122.
    destruct (is_at_most_two_digits (nth n l 0)); lia.
Qed.
Lemma sum_two_digit_upto_correct_122 : forall l k,
  0 <= k <= Zlength l ->
  sum_two_digit_upto k l =
  fold_left Z.add (filter is_at_most_two_digits (firstn (Z.to_nat k) l)) 0.
Proof.
  intros l k Hk.
  unfold sum_two_digit_upto.
  apply sum_two_digit_upto_nat_correct_122.
  rewrite Zlength_correct in Hk.
  apply Nat2Z.inj_le.
  rewrite Z2Nat.id by lia.
  lia.
Qed.
Lemma problem_122_spec_of_exit : forall l k i s,
  0 <= k <= Zlength l ->
  i = k ->
  s = sum_two_digit_upto i l ->
  problem_122_spec l k s.
Proof.
  intros l k i s Hk Hi Hs.
  subst i.
  unfold problem_122_spec.
  subst s.
  rewrite sum_two_digit_upto_correct_122 by exact Hk.
  unfold sublist.
  rewrite skipn_O.
  reflexivity.
Qed.


Lemma proof_of_p122_add_elements_safety_wit_6 : p122_add_elements_safety_wit_6.
Proof.
  pre_process.
  subst s.
  match goal with
  | H: sum_two_digit_int_range k_pre lv |- _ =>
      destruct (H i ltac:(lia) ltac:(lia)) as [_ Hsum]
  end.
  entailer!.
Qed. 

Lemma proof_of_p122_add_elements_entail_wit_1 : p122_add_elements_entail_wit_1.
Proof.
  pre_process.
Qed. 

Lemma proof_of_p122_add_elements_entail_wit_2_1 : p122_add_elements_entail_wit_2_1.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  rewrite sum_two_digit_upto_step_in by lia.
  lia.
Qed. 

Lemma proof_of_p122_add_elements_entail_wit_2_2 : p122_add_elements_entail_wit_2_2.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  rewrite sum_two_digit_upto_step_lo by lia.
  assumption.
Qed. 

Lemma proof_of_p122_add_elements_entail_wit_2_3 : p122_add_elements_entail_wit_2_3.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  rewrite sum_two_digit_upto_step_hi by lia.
  assumption.
Qed. 

Lemma proof_of_p122_add_elements_return_wit_1 : p122_add_elements_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = k_pre) by lia.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply problem_122_spec_of_exit with (i := i); auto; lia.
Qed. 

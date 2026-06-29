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
From SimpleC.EE.CAV.ground_truth_p110_exchange Require Import p110_exchange_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Arith.Arith.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p110_exchange.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p110_exchange.v so public contract files expose definitions only. *)

Lemma count_even_list_nonneg : forall l,
  0 <= count_even_list l.
Proof.
  induction l; simpl; try lia.
  destruct (even_zb a); lia.
Qed.
Lemma count_even_list_le_len : forall l,
  count_even_list l <= Zlength l.
Proof.
  induction l; simpl.
  - rewrite Zlength_nil. lia.
  - rewrite Zlength_cons.
    destruct (even_zb a); lia.
Qed.
Lemma count_even_list_app_single : forall l x,
  count_even_list (l ++ [x]) =
  count_even_list l + if even_zb x then 1 else 0.
Proof.
  induction l as [| y ys IH]; intros x; simpl.
  - lia.
  - rewrite IH.
    destruct (even_zb y); destruct (even_zb x); lia.
Qed.
Lemma count_even_upto_bounds : forall i l,
  0 <= i <= Zlength l ->
  0 <= count_even_upto i l <= i.
Proof.
  intros i l Hi.
  unfold count_even_upto.
  split.
  - apply count_even_list_nonneg.
  - pose proof (count_even_list_le_len (sublist 0 i l)).
    rewrite Zlength_sublist in H by lia.
    lia.
Qed.
Lemma count_even_upto_0 : forall l,
  count_even_upto 0 l = 0.
Proof.
  intros l.
  unfold count_even_upto, sublist.
  simpl.
  reflexivity.
Qed.
Lemma count_even_upto_full : forall l n,
  n = Zlength l ->
  count_even_upto n l = count_even_list l.
Proof.
  intros l n Hn.
  subst n.
  unfold count_even_upto.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed.
Lemma count_even_upto_step_even : forall i l,
  0 <= i < Zlength l ->
  even_zb (Znth i l 0) = true ->
  count_even_upto (i + 1) l = count_even_upto i l + 1.
Proof.
  intros i l Hi Heven.
  unfold count_even_upto.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  replace (sublist i (i + 1) l) with (Znth i l 0 :: nil).
  - rewrite count_even_list_app_single.
    rewrite Heven.
    lia.
  - symmetry. apply sublist_single. lia.
Qed.
Lemma count_even_upto_step_not_even : forall i l,
  0 <= i < Zlength l ->
  even_zb (Znth i l 0) = false ->
  count_even_upto (i + 1) l = count_even_upto i l.
Proof.
  intros i l Hi Heven.
  unfold count_even_upto.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  replace (sublist i (i + 1) l) with (Znth i l 0 :: nil).
  - rewrite count_even_list_app_single.
    rewrite Heven.
    lia.
  - symmetry. apply sublist_single. lia.
Qed.
Lemma even_zb_rem_true : forall x,
  Z.rem x 2 = 0 ->
  even_zb x = true.
Proof.
  intros x H.
  unfold even_zb.
  apply Z.eqb_eq.
  exact H.
Qed.
Lemma even_zb_rem_false : forall x,
  Z.rem x 2 <> 0 ->
  even_zb x = false.
Proof.
  intros x H.
  unfold even_zb.
  apply Z.eqb_neq.
  exact H.
Qed.
Lemma count_even_upto_step_rem_even : forall i l,
  0 <= i < Zlength l ->
  Z.rem (Znth i l 0) 2 = 0 ->
  count_even_upto (i + 1) l = count_even_upto i l + 1.
Proof.
  intros.
  apply count_even_upto_step_even; auto.
  apply even_zb_rem_true; assumption.
Qed.
Lemma count_even_upto_step_rem_not_even : forall i l,
  0 <= i < Zlength l ->
  Z.rem (Znth i l 0) 2 <> 0 ->
  count_even_upto (i + 1) l = count_even_upto i l.
Proof.
  intros.
  apply count_even_upto_step_not_even; auto.
  apply even_zb_rem_false; assumption.
Qed.
Lemma problem_110_spec_true : forall lst1 lst2 total_even,
  problem_110_pre lst1 lst2 ->
  nonnegative_list lst1 ->
  nonnegative_list lst2 ->
  total_even = count_even_list lst1 + count_even_list lst2 ->
  Zlength lst1 <= total_even ->
  problem_110_spec lst1 lst2 1.
Proof.
  intros lst1 lst2 total_even _ _ _ Htotal Hcmp.
  unfold problem_110_spec, yesno_of_110.
  replace (Z.eqb 1 1) with true by reflexivity.
  assert ((Z.leb (Zlength lst1 - count_even_list lst1) (count_even_list lst2)) = true).
  { apply Z.leb_le. lia. }
  rewrite H.
  reflexivity.
Qed.
Lemma problem_110_spec_false : forall lst1 lst2 total_even,
  problem_110_pre lst1 lst2 ->
  nonnegative_list lst1 ->
  nonnegative_list lst2 ->
  total_even = count_even_list lst1 + count_even_list lst2 ->
  total_even < Zlength lst1 ->
  problem_110_spec lst1 lst2 0.
Proof.
  intros lst1 lst2 total_even _ _ _ Htotal Hcmp.
  unfold problem_110_spec, yesno_of_110.
  replace (Z.eqb 0 1) with false by reflexivity.
  assert ((Z.leb (Zlength lst1 - count_even_list lst1) (count_even_list lst2)) = false).
  { apply Z.leb_gt. lia. }
  rewrite H.
  reflexivity.
Qed.


Ltac exchange_base :=
  pre_process;
  subst;
  entailer!;
  try rewrite count_even_upto_0;
  try lia.

Ltac exchange_step_even :=
  pre_process;
  subst;
  entailer!;
  match goal with
  | Hrem : Z.rem (Znth ?i ?l 0) 2 = 0 |- _ =>
      rewrite (count_even_upto_step_rem_even i l) by lia;
      lia
  end.

Ltac exchange_step_odd :=
  pre_process;
  subst;
  entailer!;
  match goal with
  | Hrem : Z.rem (Znth ?i ?l 0) 2 <> 0 |- _ =>
      rewrite (count_even_upto_step_rem_not_even i l) by lia;
      lia
  end.

Lemma proof_of_p110_exchange_entail_wit_1 : p110_exchange_entail_wit_1.
Proof.
  unfold p110_exchange_entail_wit_1.
  intros.
  exchange_base.
Qed. 

Lemma proof_of_p110_exchange_entail_wit_2_1 : p110_exchange_entail_wit_2_1.
Proof.
  unfold p110_exchange_entail_wit_2_1.
  intros.
  exchange_step_even.
Qed. 

Lemma proof_of_p110_exchange_entail_wit_2_2 : p110_exchange_entail_wit_2_2.
Proof.
  unfold p110_exchange_entail_wit_2_2.
  intros.
  exchange_step_odd.
Qed. 

Lemma proof_of_p110_exchange_entail_wit_3 : p110_exchange_entail_wit_3.
Proof.
  unfold p110_exchange_entail_wit_3.
  intros.
  pre_process.
  subst.
  assert (i = Zlength l1) by lia.
  subst i.
  entailer!.
Qed.

Lemma proof_of_p110_exchange_entail_wit_4 : p110_exchange_entail_wit_4.
Proof.
  unfold p110_exchange_entail_wit_4.
  intros.
  exchange_base.
Qed. 

Lemma proof_of_p110_exchange_entail_wit_5_1 : p110_exchange_entail_wit_5_1.
Proof.
  unfold p110_exchange_entail_wit_5_1.
  intros.
  exchange_step_even.
Qed. 

Lemma proof_of_p110_exchange_entail_wit_5_2 : p110_exchange_entail_wit_5_2.
Proof.
  unfold p110_exchange_entail_wit_5_2.
  intros.
  exchange_step_odd.
Qed. 

Lemma proof_of_p110_exchange_return_wit_1 : p110_exchange_return_wit_1.
Proof.
  unfold p110_exchange_return_wit_1.
  intros.
  pre_process.
  subst.
  entailer!.
  assert (i = Zlength l2) by lia.
  subst i.
  rewrite (count_even_upto_full l1 (Zlength l1) eq_refl) in *.
  rewrite (count_even_upto_full l2 (Zlength l2) eq_refl) in *.
  eapply problem_110_spec_false with (total_even := count_even_list l1 + count_even_list l2); eauto; lia.
Qed. 

Lemma proof_of_p110_exchange_return_wit_2 : p110_exchange_return_wit_2.
Proof.
  unfold p110_exchange_return_wit_2.
  intros.
  pre_process.
  subst.
  entailer!.
  assert (i = Zlength l2) by lia.
  subst i.
  rewrite (count_even_upto_full l1 (Zlength l1) eq_refl) in *.
  rewrite (count_even_upto_full l2 (Zlength l2) eq_refl) in *.
  eapply problem_110_spec_true with (total_even := count_even_list l1 + count_even_list l2); eauto; lia.
Qed. 

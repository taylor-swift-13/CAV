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
From SimpleC.EE.CAV.ground_truth_p128_prod_signs Require Import p128_prod_signs_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Lia.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p128_prod_signs.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p128_prod_signs.v so public contract files expose definitions only. *)

Lemma fold_right_add_app_single : forall (xs : list Z) (x : Z),
  fold_right Z.add 0 (xs ++ [x]) = fold_right Z.add 0 xs + x.
Proof.
  induction xs; intros x; simpl.
  - lia.
  - rewrite IHxs. lia.
Qed.
Lemma fold_right_mul_app_single : forall (xs : list Z) (x : Z),
  fold_right Z.mul 1 (xs ++ [x]) = fold_right Z.mul 1 xs * x.
Proof.
  induction xs; intros x; simpl.
  - rewrite Z.mul_comm.
    destruct x; reflexivity.
  - rewrite IHxs. rewrite Z.mul_assoc. reflexivity.
Qed.
Lemma sublist_snoc_Znth_128 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0].
Proof.
  intros.
  rewrite (sublist_split 0 (i + 1) i l).
  - replace (sublist i (i + 1) l) with [Znth i l 0].
    + reflexivity.
    + symmetry. apply sublist_single.
      lia.
  - lia.
  - lia.
Qed.
Lemma sum_abs_prefix_snoc : forall l i,
  0 <= i < Zlength l ->
  sum_abs_prefix (i + 1) l =
    sum_abs_prefix i l + Z.abs (Znth i l 0).
Proof.
  intros.
  unfold sum_abs_prefix.
  rewrite sublist_snoc_Znth_128 by lia.
  rewrite map_app.
  simpl.
  rewrite fold_right_add_app_single.
  reflexivity.
Qed.
Lemma prod_sgn_prefix_snoc : forall l i,
  0 <= i < Zlength l ->
  prod_sgn_prefix (i + 1) l =
    prod_sgn_prefix i l * Z.sgn (Znth i l 0).
Proof.
  intros.
  unfold prod_sgn_prefix.
  rewrite sublist_snoc_Znth_128 by lia.
  rewrite map_app.
  simpl.
  rewrite fold_right_mul_app_single.
  reflexivity.
Qed.
Lemma prod_sgn_prefix_bound : forall i l,
  0 <= i <= Zlength l ->
  -1 <= prod_sgn_prefix i l <= 1.
Proof.
  intros i l Hi.
  unfold prod_sgn_prefix.
  remember (sublist 0 i l) as xs.
  clear Heqxs l i Hi.
  induction xs; simpl.
  - lia.
  - pose proof (Z.sgn_spec a) as Hsgn.
    lia.
Qed.
Lemma prod_signs_prefix_init : forall l,
  0 <= Zlength l ->
  prod_signs_prefix 0 l 0 1.
Proof.
  intros.
  unfold prod_signs_prefix, sum_abs_prefix, prod_sgn_prefix.
  unfold sublist.
  simpl.
  simpl.
  repeat split; lia.
Qed.
Lemma prod_signs_prefix_zero : forall i l sum prods x,
  prod_signs_prefix i l sum prods ->
  0 <= i < Zlength l ->
  x = Znth i l 0 ->
  x = 0 ->
  prod_signs_prefix (i + 1) l (sum + Z.abs x) 0.
Proof.
  intros i l sum prods x Hpref Hi Hx Hz.
  subst x.
  unfold prod_signs_prefix in *.
  destruct Hpref as [Hbounds [Hsum Hprod]].
  repeat split; try lia.
  - rewrite sum_abs_prefix_snoc by lia. lia.
  - rewrite prod_sgn_prefix_snoc by lia. simpl. lia.
Qed.
Lemma prod_signs_prefix_neg : forall i l sum prods x,
  prod_signs_prefix i l sum prods ->
  0 <= i < Zlength l ->
  x = Znth i l 0 ->
  x < 0 ->
  prod_signs_prefix (i + 1) l (sum + Z.abs x) (- prods).
Proof.
  intros i l sum prods x Hpref Hi Hx Hneg.
  subst x.
  unfold prod_signs_prefix in *.
  destruct Hpref as [Hbounds [Hsum Hprod]].
  repeat split; try lia.
  - rewrite sum_abs_prefix_snoc by lia. lia.
  - rewrite prod_sgn_prefix_snoc by lia.
    rewrite Z.sgn_neg by lia.
    lia.
Qed.
Lemma prod_signs_prefix_pos : forall i l sum prods x,
  prod_signs_prefix i l sum prods ->
  0 <= i < Zlength l ->
  x = Znth i l 0 ->
  0 < x ->
  prod_signs_prefix (i + 1) l (sum + Z.abs x) prods.
Proof.
  intros i l sum prods x Hpref Hi Hx Hpos.
  subst x.
  unfold prod_signs_prefix in *.
  destruct Hpref as [Hbounds [Hsum Hprod]].
  repeat split; try lia.
  - rewrite sum_abs_prefix_snoc by lia. lia.
  - rewrite prod_sgn_prefix_snoc by lia.
    rewrite Z.sgn_pos by lia.
    lia.
Qed.
Lemma prod_signs_prefix_sum_range : forall i l sum prods,
  prod_signs_prefix i l sum prods ->
  prod_signs_int_range l ->
  0 <= sum <= INT_MAX.
Proof.
  intros i l sum prods Hpref [_ Hrange].
  unfold prod_signs_prefix in Hpref.
  destruct Hpref as [Hbounds [Hsum _]].
  subst sum.
  apply Hrange.
  exact Hbounds.
Qed.
Lemma prod_signs_prefix_prod_bound : forall i l sum prods,
  prod_signs_prefix i l sum prods ->
  -1 <= prods <= 1.
Proof.
  intros i l sum prods Hpref.
  unfold prod_signs_prefix in Hpref.
  destruct Hpref as [Hbounds [_ Hprod]].
  subst prods.
  apply prod_sgn_prefix_bound.
  exact Hbounds.
Qed.
Lemma prod_signs_input_int_range : forall l i,
  prod_signs_int_range l ->
  0 <= i < Zlength l ->
  INT_MIN < Znth i l 0 <= INT_MAX.
Proof.
  intros l i [Hrange _] Hi.
  apply Hrange.
  exact Hi.
Qed.
Lemma prod_signs_next_sum_range : forall i l sum prods x mag,
  prod_signs_prefix i l sum prods ->
  prod_signs_int_range l ->
  0 <= i < Zlength l ->
  x = Znth i l 0 ->
  mag = Z.abs x ->
  INT_MIN <= sum + mag <= INT_MAX.
Proof.
  intros i l sum prods x mag Hpref Hrange Hi Hx Hmag.
  subst x mag.
  destruct Hrange as [_ Hsum_range].
  unfold prod_signs_prefix in Hpref.
  destruct Hpref as [_ [Hsum _]].
  subst sum.
  pose proof (Hsum_range (i + 1)) as Hnext.
  rewrite sum_abs_prefix_snoc in Hnext by lia.
  lia.
Qed.
Lemma prod_signs_prefix_full_spec : forall l sum prods,
  l <> nil ->
  prod_signs_prefix (Zlength l) l sum prods ->
  problem_128_spec l (sum * prods).
Proof.
  intros l sum prods Hnonempty Hpref.
  unfold prod_signs_prefix in Hpref.
  destruct Hpref as [Hbounds [Hsum Hprod]].
  unfold problem_128_spec.
  destruct l.
  - contradiction.
  - rewrite Hsum, Hprod.
    unfold sum_abs_prefix, prod_sgn_prefix.
    repeat rewrite sublist_self by lia.
    reflexivity.
Qed.
Lemma problem_128_spec_empty : forall l,
  Zlength l = 0 ->
  problem_128_spec l (-32768).
Proof.
  intros l Hlen.
  destruct l; simpl; auto.
  rewrite Zlength_cons in Hlen.
  pose proof (Zlength_nonneg l).
  lia.
Qed.
Lemma problem_128_spec_nonempty : forall l sum prods,
  Zlength l > 0 ->
  prod_signs_prefix (Zlength l) l sum prods ->
  problem_128_spec l (sum * prods).
Proof.
  intros l sum prods Hlen Hpref.
  destruct l.
  - rewrite Zlength_nil in Hlen. lia.
  - apply prod_signs_prefix_full_spec; [discriminate | exact Hpref].
Qed.


Lemma proof_of_abs_return_wit_1 : abs_return_wit_1.
Proof.
  pre_process.
Qed. 

Lemma proof_of_abs_return_wit_2 : abs_return_wit_2.
Proof.
  pre_process.
Qed. 

Lemma proof_of_p128_prod_signs_safety_wit_13 : p128_prod_signs_safety_wit_13.
Proof.
  pre_process.
  pose proof (prod_signs_prefix_prod_bound _ _ _ _ H9).
  entailer!.
Qed. 

Lemma proof_of_p128_prod_signs_safety_wit_17 : p128_prod_signs_safety_wit_17.
Proof.
  pre_process.
  pose proof (prod_signs_prefix_sum_range _ _ _ _ H8 H5) as Hsum.
  pose proof (prod_signs_prefix_prod_bound _ _ _ _ H8) as Hprod.
  entailer!.
  all: nia.
Qed. 

Lemma proof_of_p128_prod_signs_entail_wit_1 : p128_prod_signs_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  apply prod_signs_prefix_init.
  lia.
Qed. 

Lemma proof_of_p128_prod_signs_entail_wit_2 : p128_prod_signs_entail_wit_2.
Proof.
  pre_process.
  assert (Hi : 0 <= i < Zlength input_l) by lia.
  pose proof (prod_signs_input_int_range input_l i H6 Hi) as Hcurrent.
  pose proof (prod_signs_next_sum_range i input_l sum prods (Znth i input_l 0) retval H9 H6 Hi eq_refl H) as Hnext.
  entailer!.
Qed. 

Lemma proof_of_p128_prod_signs_entail_wit_3_1 : p128_prod_signs_entail_wit_3_1.
Proof.
  pre_process.
  subst current.
  subst mag.
  entailer!.
  apply prod_signs_prefix_neg with (x := Znth i input_l 0); try assumption; lia.
Qed. 

Lemma proof_of_p128_prod_signs_entail_wit_3_2 : p128_prod_signs_entail_wit_3_2.
Proof.
  pre_process.
  subst current.
  subst mag.
  entailer!.
  apply prod_signs_prefix_pos with (x := Znth i input_l 0); try assumption; lia.
Qed. 

Lemma proof_of_p128_prod_signs_entail_wit_3_3 : p128_prod_signs_entail_wit_3_3.
Proof.
  pre_process.
  subst current.
  subst mag.
  entailer!.
  eapply prod_signs_prefix_zero with (prods := prods) (x := Znth i input_l 0); try assumption; lia.
Qed. 

Lemma proof_of_p128_prod_signs_return_wit_1 : p128_prod_signs_return_wit_1.
Proof.
  pre_process.
  replace i with arr_size_pre in * by lia.
  entailer!.
  apply problem_128_spec_nonempty with (sum := sum) (prods := prods).
  - lia.
  - replace (Zlength input_l) with arr_size_pre by lia.
    assumption.
Qed. 

Lemma proof_of_p128_prod_signs_return_wit_2 : p128_prod_signs_return_wit_2.
Proof.
  pre_process.
  entailer!.
  apply problem_128_spec_empty.
  lia.
Qed. 

Lemma proof_of_p128_prod_signs_partial_solve_wit_2_pure : p128_prod_signs_partial_solve_wit_2_pure.
Proof.
  pre_process.
  assert (Hi : 0 <= i < Zlength input_l) by lia.
  pose proof (prod_signs_input_int_range input_l i H5 Hi) as Hcurrent.
  entailer!.
Qed. 

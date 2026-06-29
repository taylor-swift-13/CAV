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
From SimpleC.EE.CAV.ground_truth_p104_unique_digits Require Import p104_unique_digits_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.

Import naive_C_Rules.
Require Import p104_unique_digits.
Local Open Scope sac.
Require Import Lia.
From AUXLib Require Import ListLib.

Local Open Scope list_scope.

(* Proof helpers moved from p104_unique_digits.v so public contract files expose definitions only. *)

Lemma zero_list_nat_length : forall n,
  length (zero_list_nat n) = n.
Proof.
  induction n; simpl; lia.
Qed.
Lemma zero_list_Zlength : forall n,
  0 <= n ->
  Zlength (zero_list n) = n.
Proof.
  intros n Hn.
  unfold zero_list.
  rewrite Zlength_correct.
  rewrite zero_list_nat_length.
  lia.
Qed.
Lemma problem_104_pre_Znth : forall l i,
  problem_104_pre l ->
  0 <= i < Zlength l ->
  0 < Znth i l 0 < INT_MAX.
Proof.
  intros l i Hpre Hi.
  unfold problem_104_pre in Hpre.
  rewrite Forall_forall in Hpre.
  apply Hpre.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma odd_digit_scan_state_bounds : forall original num u,
  0 <= original ->
  odd_digit_scan_state original num u ->
  0 <= num <= original /\ (u = 0 \/ u = 1).
Proof.
  intros original num u Horig Hstate.
  induction Hstate.
  - split; lia.
  - destruct IHHstate as [Hbounds Hu].
    split.
    + assert (0 <= num / 10) by (apply Z.div_pos; lia).
      assert (num / 10 <= num).
      {
        apply Z.div_le_upper_bound; lia.
      }
      lia.
    + lia.
  - destruct IHHstate as [Hbounds Hu].
    split.
    + assert (0 <= num / 10) by (apply Z.div_pos; lia).
      assert (num / 10 <= num).
      {
        apply Z.div_le_upper_bound; lia.
      }
      lia.
    + lia.
Qed.
Lemma nat_to_digits_fueled_ge_104 : forall n fuel,
  (n <= fuel)%nat ->
  nat_to_digits_fueled n fuel = nat_to_digits n.
Proof.
  apply (well_founded_induction
           lt_wf
           (fun n => forall fuel, (n <= fuel)%nat ->
              nat_to_digits_fueled n fuel = nat_to_digits n)).
  intros n IH fuel Hle.
  destruct n.
  - destruct fuel; reflexivity.
  - destruct fuel.
    + lia.
    + unfold nat_to_digits at 1.
      simpl.
      assert (Hlt : (((S n) / 10) < S n)%nat).
      { apply Nat.div_lt; lia. }
      change (((S n mod 10)%nat :: nat_to_digits_fueled (S n / 10) fuel) =
              ((S n mod 10)%nat :: nat_to_digits_fueled (S n / 10) n)).
      rewrite (IH ((S n) / 10)%nat Hlt fuel) by lia.
      rewrite (IH ((S n) / 10)%nat Hlt n).
      * reflexivity.
      * destruct n.
        -- simpl. lia.
        -- change ((S (S n) / 10 <= S n)%nat).
           apply Nat.div_le_upper_bound; lia.
Qed.
Lemma nat_to_digits_step_104 : forall n,
  n <> O ->
  nat_to_digits n = (n mod 10)%nat :: nat_to_digits (n / 10).
Proof.
  intros n Hn.
  destruct n.
  - contradiction.
  - unfold nat_to_digits at 1.
    simpl.
    rewrite nat_to_digits_fueled_ge_104.
    + reflexivity.
    + destruct n.
      * simpl. lia.
      * change ((S (S n) / 10 <= S n)%nat).
        apply Nat.div_le_upper_bound; lia.
Qed.
Lemma has_only_odd_digits_bool_step_104 : forall n,
  0 < n ->
  has_only_odd_digits_bool (Z.to_nat n) =
    andb (odd_digit_bool_104 (Z.to_nat (n mod 10)))
      (has_only_odd_digits_bool (Z.to_nat (n / 10))).
Proof.
  intros n Hpos.
  unfold has_only_odd_digits_bool.
  rewrite nat_to_digits_step_104 by lia.
  change ((fun d : nat =>
       orb (Nat.eqb d 1)
         (orb (Nat.eqb d 3)
           (orb (Nat.eqb d 5)
             (orb (Nat.eqb d 7) (Nat.eqb d 9)))))
            (Z.to_nat n mod 10)%nat) with
    (odd_digit_bool_104 (Z.to_nat (n mod 10))).
  rewrite Z2Nat.inj_mod by lia.
  rewrite Z2Nat.inj_div by lia.
  reflexivity.
Qed.
Lemma odd_digit_bool_even_false_104 : forall d,
  (d < 10)%nat ->
  (d mod 2 = 0)%nat ->
  odd_digit_bool_104 d = false.
Proof.
  intros d Hd Hmod.
  unfold odd_digit_bool_104.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
Qed.
Lemma odd_digit_bool_odd_true_104 : forall d,
  (d < 10)%nat ->
  (d mod 2 <> 0)%nat ->
  odd_digit_bool_104 d = true.
Proof.
  intros d Hd Hmod.
  unfold odd_digit_bool_104.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
  destruct d; simpl in *; try reflexivity; try lia.
Qed.
Lemma mod10_mod2_104 : forall n,
  (n mod 10) mod 2 = n mod 2.
Proof.
  intros n.
  rewrite (Z.div_mod n 10) at 2 by lia.
  rewrite Z.add_mod by lia.
  rewrite Z.mul_mod by lia.
  change (10 mod 2) with 0.
  rewrite Z.mul_0_l.
  rewrite Z.add_0_l.
  rewrite Z.mod_mod by lia.
  reflexivity.
Qed.
Lemma has_only_odd_digits_bool_even_step_104 : forall n,
  0 < n ->
  n mod 2 = 0 ->
  has_only_odd_digits_bool (Z.to_nat n) = false.
Proof.
  intros n Hpos Heven.
  rewrite has_only_odd_digits_bool_step_104 by lia.
  rewrite odd_digit_bool_even_false_104.
  - reflexivity.
  - pose proof (Z.mod_pos_bound n 10 ltac:(lia)).
    lia.
  - apply Nat2Z.inj.
    rewrite Nat2Z.inj_mod by lia.
    rewrite Z2Nat.id by (pose proof (Z.mod_pos_bound n 10 ltac:(lia)); lia).
    rewrite mod10_mod2_104.
    exact Heven.
Qed.
Lemma has_only_odd_digits_bool_odd_step_104 : forall n,
  0 < n ->
  n mod 2 <> 0 ->
  has_only_odd_digits_bool (Z.to_nat n) =
  has_only_odd_digits_bool (Z.to_nat (n / 10)).
Proof.
  intros n Hpos Hodd.
  rewrite has_only_odd_digits_bool_step_104 by lia.
  rewrite odd_digit_bool_odd_true_104.
  - reflexivity.
  - pose proof (Z.mod_pos_bound n 10 ltac:(lia)).
    lia.
  - intro Hnat.
    apply (f_equal Z.of_nat) in Hnat.
    rewrite Nat2Z.inj_mod in Hnat by lia.
    rewrite Z2Nat.id in Hnat by (pose proof (Z.mod_pos_bound n 10 ltac:(lia)); lia).
    rewrite mod10_mod2_104 in Hnat.
    contradiction.
Qed.
Lemma odd_digit_scan_state_correct_104 : forall original num u,
  odd_digit_scan_state original num u ->
  (u = 1 ->
   has_only_odd_digits_bool (Z.to_nat original) =
   has_only_odd_digits_bool (Z.to_nat num)) /\
  (u = 0 ->
   has_only_odd_digits_bool (Z.to_nat original) = false).
Proof.
  intros original num u Hstate.
  induction Hstate.
  - split; intros; try reflexivity; lia.
  - destruct IHHstate as [Hkeep _].
    split.
    + intros Hfalse. lia.
    + intros _. rewrite Hkeep by reflexivity.
      apply has_only_odd_digits_bool_even_step_104; assumption.
  - destruct IHHstate as [Hkeep Hzero].
    split.
    + intros _. rewrite Hkeep by reflexivity.
      apply has_only_odd_digits_bool_odd_step_104; assumption.
    + intros Hfalse. lia.
Qed.
Lemma only_odd_digits_done : forall original num u,
  odd_digit_scan_state original num u ->
  (u = 0 \/ u = 1) ->
  num <= 0 ->
  u <> 0 ->
  only_odd_digits original.
Proof.
  intros original num u Hstate Hu01 Hnum Hu.
  unfold only_odd_digits.
  destruct (odd_digit_scan_state_correct_104 _ _ _ Hstate) as [Hone _].
  replace u with 1 in Hone by lia.
  rewrite Hone by reflexivity.
  replace (Z.to_nat num) with O by lia.
  reflexivity.
Qed.
Lemma has_even_digit_done : forall original num u,
  odd_digit_scan_state original num u ->
  u = 0 ->
  has_even_digit original.
Proof.
  intros original num u Hstate Hu.
  unfold has_even_digit.
  destruct (odd_digit_scan_state_correct_104 _ _ _ Hstate) as [_ Hzero].
  replace u with 0 in Hzero by lia.
  apply Hzero.
  reflexivity.
Qed.
Lemma odd_scan_even_quot : forall original num,
  odd_digit_scan_state original num 1 ->
  0 < num ->
  num % 2 = 0 ->
  odd_digit_scan_state original (num ÷ 10) 0.
Proof.
  intros original num Hstate Hpos Heven.
  replace (num ÷ 10) with (num / 10).
  - apply odd_scan_even with (num := num); try assumption.
    rewrite Z.rem_mod_nonneg in Heven by lia.
    exact Heven.
  - symmetry. apply Z.quot_div_nonneg; lia.
Qed.
Lemma odd_scan_odd_quot : forall original num,
  odd_digit_scan_state original num 1 ->
  0 < num ->
  num % 2 <> 0 ->
  odd_digit_scan_state original (num ÷ 10) 1.
Proof.
  intros original num Hstate Hpos Hodd.
  replace (num ÷ 10) with (num / 10).
  - apply odd_scan_odd with (num := num); try assumption.
    intro Hmod.
    apply Hodd.
    rewrite Z.rem_mod_nonneg by lia.
    exact Hmod.
  - symmetry. apply Z.quot_div_nonneg; lia.
Qed.
Lemma filter_odd_digits_snoc_true : forall l x,
  has_only_odd_digits_bool (Z.to_nat x) = true ->
  filter_odd_digits (l ++ [x]) = filter_odd_digits l ++ [x].
Proof.
  induction l; intros x Hx; simpl.
  - rewrite Hx. reflexivity.
  - destruct (has_only_odd_digits_bool (Z.to_nat a)); simpl; rewrite IHl; auto.
Qed.
Lemma filter_odd_digits_snoc_false : forall l x,
  has_only_odd_digits_bool (Z.to_nat x) = false ->
  filter_odd_digits (l ++ [x]) = filter_odd_digits l.
Proof.
  induction l; intros x Hx; simpl.
  - rewrite Hx. reflexivity.
  - destruct (has_only_odd_digits_bool (Z.to_nat a)); simpl; rewrite IHl; auto.
Qed.
Lemma map_filter_odd_digits : forall l,
  map Z.to_nat (filter_odd_digits l) =
  filter_odd_digits_nat (map Z.to_nat l).
Proof.
  induction l; simpl.
  - reflexivity.
  - destruct (has_only_odd_digits_bool (Z.to_nat a)); simpl; rewrite IHl; reflexivity.
Qed.
Lemma unique_digits_prefix_add_step : forall input i output,
  0 <= i < Zlength input ->
  unique_digits_prefix input i output ->
  only_odd_digits (Znth i input 0) ->
  unique_digits_prefix input (i + 1) (output ++ [Znth i input 0]).
Proof.
  intros input i output Hi Hprefix Hodd.
  unfold unique_digits_prefix in *.
  destruct Hprefix as [Hbounds Hout].
  split.
  - lia.
  - rewrite Hout.
    rewrite (sublist_split 0 (i + 1) i input)
      by (try rewrite <- Zlength_correct; lia).
    rewrite (sublist_single 0 i input) by lia.
    symmetry.
    apply filter_odd_digits_snoc_true.
    exact Hodd.
Qed.
Lemma unique_digits_prefix_skip_step : forall input i output,
  0 <= i < Zlength input ->
  unique_digits_prefix input i output ->
  has_even_digit (Znth i input 0) ->
  unique_digits_prefix input (i + 1) output.
Proof.
  intros input i output Hi Hprefix Heven.
  unfold unique_digits_prefix in *.
  destruct Hprefix as [Hbounds Hout].
  split.
  - lia.
  - rewrite Hout.
    rewrite (sublist_split 0 (i + 1) i input)
      by (try rewrite <- Zlength_correct; lia).
    rewrite (sublist_single 0 i input) by lia.
    symmetry.
    apply filter_odd_digits_snoc_false.
    exact Heven.
Qed.
Lemma problem_104_spec_of_sorted : forall input filtered output,
  unique_digits_prefix input (Zlength input) filtered ->
  sorted_int_list_by 1 output ->
  Permutation filtered output ->
  problem_104_spec input output.
Proof.
  intros input filtered output Hprefix Hsorted Hperm.
  unfold problem_104_spec, unique_digits_impl.
  unfold unique_digits_prefix in Hprefix.
  destruct Hprefix as [Hbounds Hfiltered].
  unfold sorted_int_list_by in Hsorted.
  change (Z.eqb 1 0) with false in Hsorted.
  rewrite (Hsorted filtered Hperm).
  rewrite Hfiltered.
  rewrite sublist_self by lia.
  rewrite map_filter_odd_digits.
  reflexivity.
Qed.


Lemma proof_of_has_only_odd_digits_int_entail_wit_1 : has_only_odd_digits_int_entail_wit_1.
Proof.
  pre_process.
  Left.
  entailer!.
  constructor.
  lia.
Qed. 

Lemma proof_of_has_only_odd_digits_int_entail_wit_4_1 : has_only_odd_digits_int_entail_wit_4_1.
Proof.
  pre_process.
  subst u.
  Right.
  assert (0 <= num ÷ 10 <= value_pre).
  {
    assert (Hq : num ÷ 10 = num / 10) by (apply Z.quot_div_nonneg; lia).
    rewrite Hq.
    assert (0 <= num / 10) by (apply Z.div_pos; lia).
    assert (num / 10 <= num).
    {
      apply Z.div_le_upper_bound; lia.
    }
    lia.
  }
  entailer!.
  apply odd_scan_even_quot; try assumption; lia.
Qed. 

Lemma proof_of_has_only_odd_digits_int_entail_wit_4_2 : has_only_odd_digits_int_entail_wit_4_2.
Proof.
  pre_process.
  subst u.
  Left.
  assert (0 <= num ÷ 10 <= value_pre).
  {
    assert (Hq : num ÷ 10 = num / 10) by (apply Z.quot_div_nonneg; lia).
    rewrite Hq.
    assert (0 <= num / 10) by (apply Z.div_pos; lia).
    assert (num / 10 <= num).
    {
      apply Z.div_le_upper_bound; lia.
    }
    lia.
  }
  entailer!.
  apply odd_scan_odd_quot; try assumption; lia.
Qed. 

Lemma proof_of_has_only_odd_digits_int_return_wit_1 : has_only_odd_digits_int_return_wit_1.
Proof.
  pre_process.
  Right.
  entailer!.
  apply has_even_digit_done with (num := num) (u := u); assumption.
Qed. 

Lemma proof_of_has_only_odd_digits_int_return_wit_2 : has_only_odd_digits_int_return_wit_2.
Proof.
  pre_process.
  Left.
  entailer!.
  apply only_odd_digits_done with (num := num) (u := u); try assumption; lia.
Qed. 

Lemma proof_of_has_only_odd_digits_int_return_wit_3 : has_only_odd_digits_int_return_wit_3.
Proof.
  pre_process.
  Right.
  entailer!.
  apply has_even_digit_done with (num := num) (u := u); assumption.
Qed. 

Lemma proof_of_p104_unique_digits_entail_wit_1 : p104_unique_digits_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z).
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
  unfold unique_digits_prefix.
  split.
  - lia.
  - unfold sublist.
    simpl.
    reflexivity.
Qed. 

Lemma proof_of_p104_unique_digits_entail_wit_4_1 : p104_unique_digits_entail_wit_4_1.
Proof.
  pre_process.
  Exists (output_l_2 ++ (Znth i input_l 0 :: nil)).
  entailer!.
  - apply unique_digits_prefix_add_step; try assumption; lia.
  - rewrite Zlength_app.
    rewrite Zlength_cons.
    rewrite Zlength_nil.
    lia.
Qed. 

Lemma proof_of_p104_unique_digits_entail_wit_4_2 : p104_unique_digits_entail_wit_4_2.
Proof.
  pre_process.
  Exists output_l_2.
  entailer!.
  apply unique_digits_prefix_skip_step; try assumption; lia.
Qed. 

Lemma proof_of_p104_unique_digits_entail_wit_5 : p104_unique_digits_entail_wit_5.
Proof.
  pre_process.
  assert (i = x_size_pre) by lia.
  subst i.
  Exists output_l_2.
  entailer!.
Qed.

Lemma proof_of_p104_unique_digits_entail_wit_6 : p104_unique_digits_entail_wit_6.
Proof.
  pre_process.
  Exists sorted_full_l sorted_l_2 output_l_2.
  assert (problem_104_spec input_l sorted_l_2).
  {
    assert (unique_digits_prefix input_l (Zlength input_l) output_l_2).
    {
      replace (Zlength input_l) with x_size_pre by lia.
      assumption.
    }
    apply problem_104_spec_of_sorted with (filtered := output_l_2); assumption.
  }
  entailer!.
Qed. 

Lemma proof_of_p104_unique_digits_return_wit_1 : p104_unique_digits_return_wit_1.
Proof.
  pre_process.
  Exists data_l_2 sorted_l output_size_2 data_2.
  entailer!.
Qed. 

Lemma proof_of_p104_unique_digits_partial_solve_wit_4_pure : p104_unique_digits_partial_solve_wit_4_pure.
Proof.
  pre_process.
  pose proof (problem_104_pre_Znth input_l i H5 ltac:(lia)).
  entailer!.
Qed. 

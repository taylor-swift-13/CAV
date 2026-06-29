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
From SimpleC.EE.CAV.ground_truth_p025_factorize Require Import p025_factorize_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.

Import naive_C_Rules.
Require Import p025_factorize.
Local Open Scope sac.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Local Open Scope list_scope.

(* Proof helpers moved from p025_factorize.v so public contract files expose definitions only. *)

Lemma zprod_app : forall l1 l2,
  zprod (l1 ++ l2) = zprod l1 * zprod l2.
Proof.
  induction l1 as [| x xs IH]; intros l2; simpl.
  - destruct (zprod l2); reflexivity.
  - rewrite IH. ring.
Qed.
Lemma sorted_append_last : forall l x,
  Sorted Z.le l ->
  Forall (fun y => y <= x) l ->
  Sorted Z.le (l ++ [x]).
Proof.
  induction l as [| a xs IH]; intros x Hsorted Hle; simpl.
  - constructor; constructor.
  - pose proof (Sorted_inv Hsorted) as [Hsorted_tail Hhd].
    inversion Hle; subst.
    constructor.
    + apply IH; assumption.
    + destruct xs as [| b ys].
      * constructor. assumption.
      * inversion Hhd; subst. constructor. assumption.
Qed.
Lemma problem_25_spec_of_state_exit : forall n0 n factors,
  2 <= n <= n0 ->
  zprod factors * n = n0 ->
  Sorted Z.le factors ->
  Forall zprime factors ->
  Forall (fun x => 2 <= x <= n0) factors ->
  Forall (fun x => x <= n) factors ->
  zprime n ->
  problem_25_spec n0 (factors ++ [n]).
Proof.
  intros n0 n factors Hn Hprod Hsorted Hprime _ Hle_n Hnprime.
  unfold problem_25_spec.
  repeat split.
  - apply sorted_append_last; assumption.
  - rewrite zprod_app. simpl. lia.
  - apply Forall_app; split; [assumption | constructor; [assumption | constructor]].
Qed.
Lemma divisor_prime_from_no_small : forall n i,
  2 <= i ->
  Z.rem n i = 0 ->
  no_small_factor n i ->
  zprime i.
Proof.
  intros n i Hi Hdiv Hsmall.
  unfold zprime, IsPrime.
  split.
  - change (Z.to_nat 1 < Z.to_nat i)%nat.
    apply Z2Nat.inj_lt; lia.
  - intros d Hdmod.
    destruct d as [| d'].
    + simpl in Hdmod.
      assert (0 < Z.to_nat i)%nat.
      { change (Z.to_nat 0 < Z.to_nat i)%nat.
        apply Z2Nat.inj_lt; lia. }
      lia.
    + destruct d' as [| d''].
      * left; reflexivity.
      * set (dz := Z.of_nat (S (S d''))).
        assert (Hdz_ge : 2 <= dz) by lia.
        destruct (lt_eq_lt_dec (S (S d'')) (Z.to_nat i)) as [[Hd_lt | Hd_eq] | Hd_gt].
        -- exfalso.
           assert (Hdiv_i : exists c, Z.to_nat i = ((S (S d'')) * c)%nat).
           { apply (proj1 (Nat.Div0.mod_divides _ _)); exact Hdmod. }
           destruct Hdiv_i as [c Hc].
           assert (Hi_eq : i = dz * Z.of_nat c).
           { pose proof (f_equal Z.of_nat Hc) as Hz.
             rewrite Nat2Z.inj_mul in Hz.
             rewrite Z2Nat.id in Hz by lia.
             exact Hz. }
           assert (Hdz_lt_i : dz < i).
           { apply Z2Nat.inj_lt; lia. }
           apply (Hsmall dz ltac:(lia)).
           apply (proj2 (Z.rem_divide n dz ltac:(lia))).
           apply (proj1 (Z.rem_divide n i ltac:(lia))) in Hdiv.
           destruct Hdiv as [q Hn].
           exists (Z.of_nat c * q).
           rewrite Hn, Hi_eq.
           ring.
        -- right. exact Hd_eq.
        -- exfalso.
           rewrite Nat.mod_small in Hdmod by lia.
           assert (0 < Z.to_nat i)%nat.
           { change (Z.to_nat 0 < Z.to_nat i)%nat.
             apply Z2Nat.inj_lt; lia. }
           lia.
Qed.
Lemma no_small_factor_after_div : forall n i,
  2 <= i ->
  Z.rem n i = 0 ->
  no_small_factor n i ->
  no_small_factor (n ÷ i) i.
Proof.
  intros n i Hi Hdiv Hsmall d Hd.
  intro Hrem.
  apply (Hsmall d Hd).
  apply (proj2 (Z.rem_divide n d ltac:(lia))).
  apply (proj1 (Z.rem_divide (n ÷ i) d ltac:(lia))) in Hrem.
  destruct Hrem as [q Hq].
  assert (Hn : n = i * (n ÷ i)).
  { apply Z.quot_exact; lia. }
  exists (i * q).
  rewrite Hn, Hq.
  ring.
Qed.
Lemma no_small_factor_after_skip : forall n i,
  2 <= i ->
  Z.rem n i <> 0 ->
  no_small_factor n i ->
  no_small_factor n (i + 1).
Proof.
  intros n i Hi Hnot Hsmall d Hd.
  assert (d < i \/ d = i) by lia.
  destruct H as [Hd_lt | ->].
  - apply Hsmall; lia.
  - exact Hnot.
Qed.
Lemma Forall_app_intro_local : forall {A} (P : A -> Prop) l1 l2,
  Forall P l1 ->
  Forall P l2 ->
  Forall P (l1 ++ l2).
Proof.
  intros A P l1 l2 H1 H2.
  induction H1; simpl; auto using Forall.
Qed.
Lemma Forall_le_bound_trans : forall l a b,
  a <= b ->
  Forall (fun x : Z => x <= a) l ->
  Forall (fun x : Z => x <= b) l.
Proof.
  intros l a b Hab H.
  induction H; constructor; auto.
  lia.
Qed.
Lemma final_prime_from_no_small_exit : forall n i,
  2 <= n ->
  2 <= i ->
  i > n ÷ i ->
  no_small_factor n i ->
  zprime n.
Proof.
  intros n i Hn Hi Hexit Hsmall.
  unfold zprime, IsPrime.
  assert (Hn_lt_square : n < i * i).
  { pose proof (Z.mul_succ_quot_gt n i ltac:(lia) ltac:(lia)) as Hlt.
    assert (Z.succ (n ÷ i) <= i) by lia.
    nia. }
  split.
  - change (Z.to_nat 1 < Z.to_nat n)%nat.
    apply Z2Nat.inj_lt; lia.
  - intros d Hdmod.
    destruct d as [| d'].
    + simpl in Hdmod.
      assert (0 < Z.to_nat n)%nat.
      { change (Z.to_nat 0 < Z.to_nat n)%nat.
        apply Z2Nat.inj_lt; lia. }
      lia.
    + destruct d' as [| d''].
      * left; reflexivity.
      * set (dz := Z.of_nat (S (S d''))).
        assert (Hdz_ge : 2 <= dz) by lia.
        destruct (lt_eq_lt_dec (S (S d'')) (Z.to_nat n)) as [[Hd_lt | Hd_eq] | Hd_gt].
        -- assert (Hdiv_n : exists c, Z.to_nat n = ((S (S d'')) * c)%nat).
           { apply (proj1 (Nat.Div0.mod_divides _ _)); exact Hdmod. }
           destruct Hdiv_n as [c Hc].
           assert (Hc_pos : (0 < c)%nat).
           { destruct c; simpl in Hc; lia. }
           assert (Hc_ge_2_or_d_small : dz < i \/ Z.of_nat c < i).
           {
             assert (Hn_eq : n = dz * Z.of_nat c).
             { pose proof (f_equal Z.of_nat Hc) as Hz.
               rewrite Nat2Z.inj_mul in Hz.
               rewrite Z2Nat.id in Hz by lia.
               exact Hz. }
             destruct c as [| c']; [lia |].
             destruct c' as [| c''].
             { right; simpl; lia. }
             assert (2 <= Z.of_nat (S (S c''))) by lia.
             assert (Hsmall_factor : dz < i \/ Z.of_nat (S (S c'')) < i) by nia.
             destruct Hsmall_factor as [Hleft | Hright]; [left | right]; assumption.
           }
           destruct Hc_ge_2_or_d_small as [Hd_small | Hc_small].
           ++ exfalso.
              apply (Hsmall dz ltac:(lia)).
              apply (proj2 (Z.rem_divide n dz ltac:(lia))).
              exists (Z.of_nat c).
              pose proof (f_equal Z.of_nat Hc) as Hz.
              rewrite Nat2Z.inj_mul in Hz.
              rewrite Z2Nat.id in Hz by lia.
              subst dz.
              rewrite Hz.
              ring.
           ++ exfalso.
              assert (Hc_ge2 : 2 <= Z.of_nat c).
              { destruct c as [| c']; [lia |].
                destruct c' as [| c'']; simpl in Hc; lia. }
              apply (Hsmall (Z.of_nat c) ltac:(lia)).
              apply (proj2 (Z.rem_divide n (Z.of_nat c) ltac:(lia))).
              exists dz.
              pose proof (f_equal Z.of_nat Hc) as Hz.
              rewrite Nat2Z.inj_mul in Hz.
              rewrite Z2Nat.id in Hz by lia.
              subst dz.
              rewrite Hz.
              ring.
        -- right. exact Hd_eq.
        -- exfalso.
           rewrite Nat.mod_small in Hdmod by lia.
           assert (0 < Z.to_nat n)%nat.
           { change (Z.to_nat 0 < Z.to_nat n)%nat.
             apply Z2Nat.inj_lt; lia. }
           lia.
Qed.


Lemma proof_of_p025_factorize_entail_wit_1 : p025_factorize_entail_wit_1.
Proof.
  pre_process.
  subst.
  Exists (@nil Z) 0.
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
  unfold factorize_loop_state.
  rewrite Zlength_nil.
  simpl.
  repeat split; try lia; try constructor.
  - destruct n0; reflexivity.
  - unfold no_small_factor.
    intros d Hd.
    lia.
Qed.

Lemma proof_of_p025_factorize_entail_wit_2_1 : p025_factorize_entail_wit_2_1.
Proof.
  pre_process.
  assert (Hq_pos: 2 <= n ÷ i) by lia.
  assert (Hq_le_n0: n ÷ i <= n0).
  { assert (Hq_lt: n ÷ i < n) by (apply Z.quot_lt; lia).
    lia. }
  assert (Hsize_next: size_2 + 1 < n0).
  { assert (Hq_ge_1: 1 <= n ÷ i) by lia.
    lia. }
  assert (Hsum_next: size_2 + 1 + n ÷ i <= n0).
  { assert (Hquot_exact: n = i * (n ÷ i)).
    { apply Z.quot_exact; lia. }
    nia. }
  Exists (factors_2 ++ i :: nil) (size_2 + 1).
  entailer!.
  - unfold factorize_loop_state in *.
    destruct H12 as
      [? [? [? [HForall [Hprod [Hsorted [Hprime [Hle_i [Hle_n Hsmall]]]]]]]]].
    assert (Hexact : n = i * (n ÷ i)).
    { apply Z.quot_exact; lia. }
    assert (Hi_prime : zprime i).
    { eapply divisor_prime_from_no_small; eauto; lia. }
    replace (i - 1 + 1) with i by lia.
    rewrite Zlength_app.
    change (Zlength (i :: nil)) with 1.
    repeat split; try lia.
    + apply Forall_app_intro_local; [exact HForall | constructor; [lia | constructor]].
    + rewrite zprod_app. simpl. rewrite Z.mul_1_r. nia.
    + apply sorted_append_last; assumption.
    + apply Forall_app_intro_local; [exact Hprime | constructor; [exact Hi_prime | constructor]].
    + apply Forall_app_intro_local; [exact Hle_i | constructor; [lia | constructor]].
    + apply Forall_app_intro_local.
      * apply Forall_le_bound_trans with (a := i); assumption.
      * constructor; [lia | constructor].
    + apply no_small_factor_after_div; assumption || lia.
  - rewrite Zlength_app.
    change (Zlength (i :: nil)) with 1.
    lia.
Qed.

Lemma proof_of_p025_factorize_entail_wit_2_2 : p025_factorize_entail_wit_2_2.
Proof.
  pre_process.
  assert (Hi_next: i + 1 <= n0).
  { assert (Hq_lt: n ÷ i < n) by (apply Z.quot_lt; lia).
    lia. }
  Exists factors_2 size_2.
  entailer!.
  unfold factorize_loop_state in *.
  destruct H12 as
    [? [? [? [HForall [Hprod [Hsorted [Hprime [Hle_i [Hle_n Hsmall]]]]]]]]].
  repeat split; try lia; try assumption.
  - apply Forall_le_bound_trans with (a := i); assumption || lia.
  - apply no_small_factor_after_skip; assumption || lia.
Qed.

Lemma proof_of_p025_factorize_return_wit_1 : p025_factorize_return_wit_1.
Proof.
  pre_process.
  Exists data_2 (factors ++ n :: nil) (size + 1).
  entailer!.
  - unfold factorize_loop_state in H11.
    destruct H11 as
      [? [? [? [HForall [Hprod [Hsorted [Hprime [Hle_i [Hle_n Hsmall]]]]]]]]].
    apply problem_25_spec_of_state_exit; try assumption; try lia.
    apply final_prime_from_no_small_exit with (i := i); assumption || lia.
  - rewrite Zlength_app.
    change (Zlength (n :: nil)) with 1.
    lia.
Qed.

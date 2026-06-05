Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260605_073258v_ex_collatz_steps Require Import ex_collatz_steps_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import ex_collatz_steps.
Local Open Scope sac.

Lemma ex_collatz_steps_fuel_unfold :
  forall n fuel,
    0 <= fuel ->
    ex_collatz_steps_fuel n (fuel + 1) =
    if Z.eqb n 1 then 0 else 1 + ex_collatz_steps_fuel (ex_collatz_next n) fuel.
Proof.
  intros n fuel Hfuel.
  unfold ex_collatz_steps_fuel.
  rewrite Z2Nat.inj_add by lia.
  simpl.
  rewrite Nat.add_1_r.
  reflexivity.
Qed.

Lemma ex_collatz_safe_fuel_unfold :
  forall n fuel,
    0 <= fuel ->
    ex_collatz_safe_fuel n (fuel + 1) =
    (1 <= n <= 9223372036854775807 /\
     if Z.eqb n 1 then
       True
     else if Z.even n then
       ex_collatz_safe_fuel (Z.div n 2) fuel
     else
       n <= 3074457345618258602 /\ ex_collatz_safe_fuel (3 * n + 1) fuel).
Proof.
  intros n fuel Hfuel.
  unfold ex_collatz_safe_fuel.
  rewrite Z2Nat.inj_add by lia.
  simpl.
  rewrite Nat.add_1_r.
  reflexivity.
Qed.

Lemma rem2_zero_even_true : forall x, Z.rem x 2 = 0 -> Z.even x = true.
Proof.
  intros x Hmod.
  apply Z.even_spec.
  apply Z.rem_divide in Hmod; [| lia].
  destruct Hmod as [k Hk].
  exists k.
  lia.
Qed.

Lemma rem2_nonzero_even_false :
  forall x, Z.rem x 2 <> 0 -> Z.even x = false.
Proof.
  intros x Hmod.
  destruct (Z.even x) eqn:Heven; auto.
  exfalso.
  apply Hmod.
  apply Z.even_spec in Heven.
  destruct Heven as [k Hk].
  subst x.
  rewrite Z.mul_comm.
  apply Z.rem_mul; lia.
Qed.

Lemma ex_collatz_safe_fuel_nonterminal_positive :
  forall n fuel,
    0 <= fuel ->
    n <> 1 ->
    ex_collatz_safe_fuel n fuel ->
    0 < fuel.
Proof.
  intros n fuel Hfuel Hneq.
  unfold ex_collatz_safe_fuel.
  destruct (Z.to_nat fuel) eqn:Hnat; simpl; intros Hsafe.
  - rewrite <- Z2Nat.id with (n := fuel) in Hnat by lia.
    lia.
  - lia.
Qed.

Lemma ex_collatz_even_safe_step :
  forall x rem,
    0 <= rem ->
    x <> 1 ->
    Z.rem x 2 = 0 ->
    ex_collatz_safe_fuel x (rem + 1) ->
    1 <= x <= 9223372036854775807 /\ ex_collatz_safe_fuel (x / 2) rem.
Proof.
  intros x rem Hrem Hneq Hmod Hsafe.
  rewrite ex_collatz_safe_fuel_unfold in Hsafe by lia.
  assert (Heq1 : Z.eqb x 1 = false) by (apply Z.eqb_neq; exact Hneq).
  rewrite Heq1 in Hsafe.
  assert (Heven : Z.even x = true) by (apply rem2_zero_even_true; exact Hmod).
  rewrite Heven in Hsafe.
  exact Hsafe.
Qed.

Lemma ex_collatz_even_steps_step :
  forall x rem,
    0 <= rem ->
    x <> 1 ->
    Z.rem x 2 = 0 ->
    ex_collatz_steps_fuel x (rem + 1) =
    1 + ex_collatz_steps_fuel (x / 2) rem.
Proof.
  intros x rem Hrem Hneq Hmod.
  rewrite ex_collatz_steps_fuel_unfold by lia.
  assert (Heq1 : Z.eqb x 1 = false) by (apply Z.eqb_neq; exact Hneq).
  rewrite Heq1.
  assert (Heven : Z.even x = true) by (apply rem2_zero_even_true; exact Hmod).
  unfold ex_collatz_next.
  rewrite Heven.
  reflexivity.
Qed.

Lemma ex_collatz_odd_safe_step :
  forall x rem,
    0 <= rem ->
    x <> 1 ->
    Z.rem x 2 <> 0 ->
    ex_collatz_safe_fuel x (rem + 1) ->
    1 <= x <= 9223372036854775807 /\
    x <= 3074457345618258602 /\
    ex_collatz_safe_fuel (3 * x + 1) rem.
Proof.
  intros x rem Hrem Hneq Hmod Hsafe.
  rewrite ex_collatz_safe_fuel_unfold in Hsafe by lia.
  assert (Heq1 : Z.eqb x 1 = false) by (apply Z.eqb_neq; exact Hneq).
  rewrite Heq1 in Hsafe.
  assert (Heven : Z.even x = false).
  { apply rem2_nonzero_even_false. exact Hmod. }
  rewrite Heven in Hsafe.
  tauto.
Qed.

Lemma ex_collatz_odd_steps_step :
  forall x rem,
    0 <= rem ->
    x <> 1 ->
    Z.rem x 2 <> 0 ->
    ex_collatz_steps_fuel x (rem + 1) =
    1 + ex_collatz_steps_fuel (3 * x + 1) rem.
Proof.
  intros x rem Hrem Hneq Hmod.
  rewrite ex_collatz_steps_fuel_unfold by lia.
  assert (Heq1 : Z.eqb x 1 = false) by (apply Z.eqb_neq; exact Hneq).
  rewrite Heq1.
  assert (Heven : Z.even x = false).
  { apply rem2_nonzero_even_false. exact Hmod. }
  unfold ex_collatz_next.
  rewrite Heven.
  reflexivity.
Qed.

Lemma ex_collatz_steps_fuel_at_one :
  forall fuel, 0 <= fuel -> ex_collatz_steps_fuel 1 fuel = 0.
Proof.
  intros fuel Hfuel.
  unfold ex_collatz_steps_fuel.
  destruct (Z.to_nat fuel); reflexivity.
Qed.

Lemma proof_of_ex_collatz_steps_safety_wit_8 : ex_collatz_steps_safety_wit_8.
Proof.
  pre_process.
  assert (Hpos : 0 < fuel - steps) by
    (eapply ex_collatz_safe_fuel_nonterminal_positive; eauto; lia).
  assert (Hrem : 0 <= fuel - steps - 1) by lia.
  replace (fuel - steps) with ((fuel - steps - 1) + 1) in H3 by lia.
  pose proof (ex_collatz_odd_safe_step x (fuel - steps - 1) Hrem H0 H H3) as Hodd.
  destruct Hodd as [[Hxlo Hxhi] [Hbound _]].
  entailer!; lia.
Qed.

Lemma proof_of_ex_collatz_steps_safety_wit_9 : ex_collatz_steps_safety_wit_9.
Proof.
  pre_process.
  assert (Hpos : 0 < fuel - steps) by
    (eapply ex_collatz_safe_fuel_nonterminal_positive; eauto; lia).
  assert (Hrem : 0 <= fuel - steps - 1) by lia.
  replace (fuel - steps) with ((fuel - steps - 1) + 1) in H3 by lia.
  pose proof (ex_collatz_odd_safe_step x (fuel - steps - 1) Hrem H0 H H3) as Hodd.
  destruct Hodd as [[Hxlo Hxhi] [Hbound _]].
  entailer!; lia.
Qed.

Lemma proof_of_ex_collatz_steps_safety_wit_12 : ex_collatz_steps_safety_wit_12.
Proof.
  pre_process.
  assert (Hpos : 0 < fuel - steps) by
    (eapply ex_collatz_safe_fuel_nonterminal_positive; eauto; lia).
  entailer!; lia.
Qed.

Lemma proof_of_ex_collatz_steps_safety_wit_13 : ex_collatz_steps_safety_wit_13.
Proof.
  pre_process.
  assert (Hpos : 0 < fuel - steps) by
    (eapply ex_collatz_safe_fuel_nonterminal_positive; eauto; lia).
  entailer!; lia.
Qed.

Lemma proof_of_ex_collatz_steps_entail_wit_1 : ex_collatz_steps_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  - replace (fuel - 0) with fuel by lia. lia.
  - replace (fuel - 0) with fuel by lia. exact H2.
Qed.

Lemma proof_of_ex_collatz_steps_entail_wit_2_1 : ex_collatz_steps_entail_wit_2_1.
Proof.
  pre_process.
  assert (Hpos : 0 < fuel - steps) by
    (eapply ex_collatz_safe_fuel_nonterminal_positive; eauto; lia).
  assert (Hrem : 0 <= fuel - (steps + 1)) by lia.
  assert (Heq : fuel - steps = (fuel - (steps + 1)) + 1) by lia.
  assert (Hxlo : 1 <= x).
  { rewrite Heq in H3.
    pose proof (ex_collatz_even_safe_step x (fuel - (steps + 1)) Hrem H0 H H3) as [[Hxlo _] _].
    exact Hxlo.
  }
  replace (x ÷ 2) with (x / 2) by
    (symmetry; apply Z.quot_div_nonneg; lia).
  assert (Hchild: ex_collatz_safe_fuel (x / 2) (fuel - (steps + 1))).
  { rewrite Heq in H3.
    pose proof (ex_collatz_even_safe_step x (fuel - (steps + 1)) Hrem H0 H H3) as [_ Hchild].
    exact Hchild.
  }
  assert (Hstep:
    ex_collatz_steps_fuel x (fuel - steps) =
    1 + ex_collatz_steps_fuel (x / 2) (fuel - (steps + 1))).
  { rewrite Heq.
    apply ex_collatz_even_steps_step; auto.
  }
  assert (Hsum':
    (steps + 1) + ex_collatz_steps_fuel (x / 2) (fuel - (steps + 1)) =
    ex_collatz_steps_fuel n_pre fuel).
  { rewrite Hstep in H4. lia. }
  entailer!; lia.
Qed.

Lemma proof_of_ex_collatz_steps_entail_wit_2_2 : ex_collatz_steps_entail_wit_2_2.
Proof.
  pre_process.
  assert (Hpos : 0 < fuel - steps) by
    (eapply ex_collatz_safe_fuel_nonterminal_positive; eauto; lia).
  assert (Hrem : 0 <= fuel - (steps + 1)) by lia.
  assert (Heq : fuel - steps = (fuel - (steps + 1)) + 1) by lia.
  assert (Hchild: ex_collatz_safe_fuel (3 * x + 1) (fuel - (steps + 1))).
  { rewrite Heq in H3.
    pose proof (ex_collatz_odd_safe_step x (fuel - (steps + 1)) Hrem H0 H H3) as [_ [_ Hchild]].
    exact Hchild.
  }
  assert (Hstep:
    ex_collatz_steps_fuel x (fuel - steps) =
    1 + ex_collatz_steps_fuel (3 * x + 1) (fuel - (steps + 1))).
  { rewrite Heq.
    apply ex_collatz_odd_steps_step; auto.
  }
  assert (Hsum':
    (steps + 1) + ex_collatz_steps_fuel (3 * x + 1) (fuel - (steps + 1)) =
    ex_collatz_steps_fuel n_pre fuel).
  { rewrite Hstep in H4. lia. }
  entailer!; lia.
Qed.

Lemma proof_of_ex_collatz_steps_return_wit_1 : ex_collatz_steps_return_wit_1.
Proof.
  pre_process.
  rewrite H in H3.
  assert (Hstep0 : ex_collatz_steps_fuel 1 (fuel - steps) = 0).
  { apply ex_collatz_steps_fuel_at_one. lia. }
  rewrite Hstep0 in H3.
  entailer!; lia.
Qed.

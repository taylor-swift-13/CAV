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
From SimpleC.EE.CAV.ground_truth_p076_is_simple_power Require Import p076_is_simple_power_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import ZArith.
Require Import ZArith.Zpow_facts.

Import naive_C_Rules.
Require Import p076_is_simple_power.
Local Open Scope sac.
Require Import Coq.micromega.Lia.
From AUXLib Require Import int_auto.

Local Open Scope list_scope.

(* Proof helpers moved from p076_is_simple_power.v so public contract files expose definitions only. *)

Lemma sp_inv_init :
  forall x n,
    sp_inv x n 0 1.
Proof.
  intros x n.
  unfold sp_inv.
  split.
  - lia.
  - split.
    + rewrite Z.pow_0_r. reflexivity.
    + intros k Hk.
      lia.
Qed.
Lemma sp_inv_step :
  forall x n count p,
    sp_inv x n count p ->
    p <> x ->
    sp_inv x n (count + 1) (p * n).
Proof.
  intros x n count p Hinv Hpneq.
  unfold sp_inv in *.
  destruct Hinv as [Hc0 [Hp Hno]].
  repeat split.
  - lia.
  - rewrite Hp.
    replace (n ^ (count + 1)) with (n ^ count * n).
    + ring.
    + rewrite Z.pow_add_r by lia.
      rewrite Z.pow_1_r.
      ring.
  - intros k Hk.
    assert (Hsplit : k < count \/ k = count) by lia.
    destruct Hsplit as [Hlt | Heq].
    + apply Hno. lia.
    + subst k.
      intro Hpow.
      apply Hpneq.
      rewrite Hp.
      exact Hpow.
Qed.
Lemma sp_inv_hit_witness :
  forall x n count p,
    sp_inv x n count p ->
    p = x ->
    count < 100 ->
    exists k : nat, x = n ^ Z.of_nat k.
Proof.
  intros x n count p Hinv Hpeq Hlt100.
  unfold sp_inv in Hinv.
  destruct Hinv as [Hc0 [Hp _]].
  exists (Z.to_nat count).
  assert (Hcount : Z.of_nat (Z.to_nat count) = count) by (apply Z2Nat.id; lia).
  rewrite Hcount.
  assert (Hx : x = n ^ count).
  {
    rewrite <- Hpeq.
    exact Hp.
  }
  exact Hx.
Qed.
Lemma no_power_if_gt :
  forall x n count p,
    sp_inv x n count p ->
    p > x ->
    1 <= n ->
    ~(exists k : nat, x = n ^ Z.of_nat k).
Proof.
  intros x n count p Hinv Hpgt Hn1 Hex.
  unfold sp_inv in Hinv.
  destruct Hinv as [Hc0 [Hp Hno]].
  destruct Hex as [k Hxk].
  set (kz := Z.of_nat k).
  assert (Hsplit : kz < count \/ count <= kz) by lia.
  destruct Hsplit as [Hlt | Hge].
  - specialize (Hno kz).
    assert (Hneq : n ^ kz <> x) by (apply Hno; lia).
    apply Hneq.
    subst kz.
    symmetry.
    exact Hxk.
  - subst kz.
    assert (Hmono : n ^ count <= n ^ Z.of_nat k).
    {
      apply Z.pow_le_mono_r; lia.
    }
    rewrite <- Hp in Hmono.
    rewrite <- Hxk in Hmono.
    lia.
Qed.
Lemma no_power_if_cutoff :
  forall x n count p,
    sp_inv x n count p ->
    count >= 100 ->
    p <= x ->
    x <= 2147483647 ->
    1 <= n ->
    ~(exists k : nat, x = n ^ Z.of_nat k).
Proof.
  intros x n count p Hinv Hc100 Hpx Hxmax Hn1 Hex.
  unfold sp_inv in Hinv.
  destruct Hinv as [Hc0 [Hp Hno]].
  destruct (Z_lt_ge_dec n 2) as [Hnlt2 | Hnge2].
  - assert (Hn1eq : n = 1) by lia.
    subst n.
    destruct Hex as [k Hxk].
    assert (Hx1 : x = 1).
    {
      rewrite Z.pow_1_l in Hxk by lia.
      exact Hxk.
    }
    assert (Hneq : 1 ^ 0 <> x).
    {
      apply Hno.
      lia.
    }
    rewrite Z.pow_0_r in Hneq.
    apply Hneq.
    symmetry.
    exact Hx1.
  - assert (H31 : 2 ^ 31 = 2147483648) by (vm_compute; reflexivity).
    assert (Hpow2_31 : 2147483647 < 2 ^ 31).
    {
      rewrite H31.
      lia.
    }
    assert (Hpow2_100 : 2 ^ 31 <= 2 ^ 100) by (apply Z.pow_le_mono_r; lia).
    assert (Hpow2 : 2147483647 < 2 ^ 100) by lia.
    assert (Hbase : 2 ^ 100 <= n ^ 100) by (apply Z.pow_le_mono_l; lia).
    assert (Hexp : n ^ 100 <= n ^ count) by (apply Z.pow_le_mono_r; lia).
    assert (Hintmax_lt_p : 2147483647 < p).
    {
      rewrite Hp.
      eapply Z.lt_le_trans; [exact Hpow2 |].
      eapply Z.le_trans; [exact Hbase | exact Hexp].
    }
    lia.
Qed.


Lemma proof_of_p076_is_simple_power_safety_wit_5 : p076_is_simple_power_safety_wit_5.
Proof.
  unfold p076_is_simple_power_safety_wit_5.
  intros.
  Intros.
  entailer!.
Qed.

Lemma proof_of_p076_is_simple_power_entail_wit_1 : p076_is_simple_power_entail_wit_1.
Proof.
  unfold p076_is_simple_power_entail_wit_1.
  intros.
  Intros.
  entailer!.
  all: first [apply sp_inv_init | lia].
Qed.

Lemma proof_of_p076_is_simple_power_entail_wit_2 : p076_is_simple_power_entail_wit_2.
Proof.
  unfold p076_is_simple_power_entail_wit_2.
  intros.
  Intros.
  entailer!.
  all: first
       [ match goal with
         | |- 1 <= ?a * ?b =>
             assert (0 < a) by lia;
             assert (0 < b) by lia;
             pose proof (Z.mul_pos_pos a b H H0) as Hpos;
             lia
         end
       | match goal with
         | |- sp_inv _ _ _ _ =>
             eapply sp_inv_step; eauto; lia
         end
       | lia ].
Qed.

Lemma proof_of_p076_is_simple_power_return_wit_1 : p076_is_simple_power_return_wit_1.
Proof.
  unfold p076_is_simple_power_return_wit_1.
  intros.
  Intros.
  entailer!.
  unfold is_simple_power_spec.
  split.
  - intro Hfalse. lia.
  - intro Hex.
    exfalso.
    eapply no_power_if_gt; eauto; lia.
Qed.

Lemma proof_of_p076_is_simple_power_return_wit_2 : p076_is_simple_power_return_wit_2.
Proof.
  unfold p076_is_simple_power_return_wit_2.
  intros.
  Intros.
  entailer!.
  unfold is_simple_power_spec.
  split.
  - intro Hfalse. lia.
  - intro Hex.
    exfalso.
    apply (no_power_if_cutoff x_pre n_pre count p); try assumption; try lia.
Qed.

Lemma proof_of_p076_is_simple_power_return_wit_3 : p076_is_simple_power_return_wit_3.
Proof.
  unfold p076_is_simple_power_return_wit_3.
  intros.
  Intros.
  entailer!.
  unfold is_simple_power_spec.
  split.
  - intros _.
    eapply sp_inv_hit_witness; eauto; lia.
  - intros _.
    lia.
Qed.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260607_092554_p076_is_simple_power Require Import p076_is_simple_power_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import ZArith.Zpow_facts.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p076_is_simple_power.
Local Open Scope sac.

Lemma proof_of_p076_is_simple_power_safety_wit_5 : p076_is_simple_power_safety_wit_5.
Proof.
  pre_process.
Qed.

Lemma proof_of_p076_is_simple_power_entail_wit_1 : p076_is_simple_power_entail_wit_1.
Proof.
  pre_process.
  unfold sp_inv.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. exact H.
    + dump_pre_spatial. exact H0.
    + dump_pre_spatial. exact H1.
    + dump_pre_spatial. exact H2.
    + dump_pre_spatial. exact H3.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      split; [lia|].
      split.
      * rewrite Z.pow_0_r by lia. reflexivity.
      * intros k Hk. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. nia.
Qed.

Lemma proof_of_p076_is_simple_power_entail_wit_2 : p076_is_simple_power_entail_wit_2.
Proof.
  pre_process.
Qed.

Lemma proof_of_p076_is_simple_power_entail_wit_3 : p076_is_simple_power_entail_wit_3.
Proof.
  pre_process.
  unfold sp_inv in *.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      destruct H8 as [Hcount [Hp Hnomatch]].
      split.
      * lia.
      * split.
        -- rewrite Hp.
           replace (n_pre ^ (count + 1)) with (n_pre * n_pre ^ count).
           ++ nia.
           ++ symmetry. apply Z.pow_succ_r. lia.
        -- intros k Hk.
           destruct Hk as [Hk0 Hklt].
           destruct (Z.eq_dec k count) as [->|Hneq].
           ++ replace (count + 1 - 1) with count by lia.
              lia.
           ++ assert (k < count) by lia.
              specialize (Hnomatch k).
              replace (count + 1 - 1) with count in Hnomatch by lia.
              apply Hnomatch; lia.
    + dump_pre_spatial. nia.
    + dump_pre_spatial. nia.
Qed.

Lemma proof_of_p076_is_simple_power_return_wit_1 : p076_is_simple_power_return_wit_1.
Proof.
  pre_process.
  unfold is_simple_power_spec.
  match goal with
  | Hinv : sp_inv _ _ _ _ |- _ =>
      unfold sp_inv in Hinv;
      destruct Hinv as [Hcount [Hp Hnomatch]]
  end.
  split_pure_spatial.
  - cancel.
  - split.
    + intro Hfalse.
      contradiction.
    + intro Hpow.
      destruct Hpow as [k Hx].
      destruct (Z_lt_ge_dec (Z.of_nat k) count) as [Hlt|Hge].
      * specialize (Hnomatch (Z.of_nat k)).
        rewrite Hx in Hnomatch.
        exfalso.
        apply (Hnomatch ltac:(lia)).
        reflexivity.
      * destruct (Z.eq_dec n_pre 1) as [->|Hn1].
        -- assert (Hp1 : p = 1).
           { rewrite Hp. rewrite Z.pow_1_l by lia. reflexivity. }
           assert (Hx1 : x_pre = 1).
           { rewrite Hx. rewrite Z.pow_1_l by lia. reflexivity. }
           exfalso; lia.
        -- assert (Hn2 : 2 <= n_pre) by lia.
           assert (Hpow_mono : n_pre ^ count <= n_pre ^ Z.of_nat k) by (apply Z.pow_le_mono_r; lia).
           rewrite <- Hx in Hpow_mono.
           exfalso; lia.
Qed.

Lemma proof_of_p076_is_simple_power_return_wit_2 : p076_is_simple_power_return_wit_2.
Proof.
  pre_process.
  unfold is_simple_power_spec.
  match goal with
  | Hinv : sp_inv _ _ _ _ |- _ =>
      unfold sp_inv in Hinv;
      destruct Hinv as [Hcount [Hp Hnomatch]]
  end.
  assert (Hcount100 : count = 100) by lia.
  subst count.
  split_pure_spatial.
  - cancel.
  - split.
    + intro Hfalse.
      contradiction.
    + intro Hpow.
      destruct (Z.eq_dec n_pre 1) as [->|Hn1].
      * destruct Hpow as [k Hx].
        assert (Hbad := Hnomatch 0).
        replace (1 ^ 0) with 1 in Hbad by reflexivity.
        assert (Hx1 : x_pre = 1).
        { rewrite Hx. rewrite Z.pow_1_l by lia. reflexivity. }
        rewrite Hx1 in Hbad.
        exfalso.
        apply (Hbad ltac:(lia)).
        reflexivity.
      * assert (Hn2 : 2 <= n_pre) by lia.
        assert (Hpow100 : 2 ^ 100 <= n_pre ^ 100) by (apply Z.pow_le_mono_l; lia).
        assert (Hpow2 : INT_MAX < 2 ^ 100).
        { change (2 ^ 100) with 1267650600228229401496703205376; lia. }
        assert (Hbig : INT_MAX < n_pre ^ 100) by (eapply Z.lt_le_trans; [exact Hpow2 | exact Hpow100]).
        assert (Hpbig : INT_MAX < p) by (rewrite Hp; exact Hbig).
        assert (Hple : p <= INT_MAX) by (eapply Z.le_trans; [exact H0 | exact H2]).
        exfalso; lia.
Qed.

Lemma proof_of_p076_is_simple_power_return_wit_3 : p076_is_simple_power_return_wit_3.
Proof.
  pre_process.
  unfold is_simple_power_spec.
  match goal with
  | Hinv : sp_inv _ _ _ _ |- _ =>
      unfold sp_inv in Hinv;
      destruct Hinv as [Hcount [Hp Hnomatch]]
  end.
  split_pure_spatial.
  - cancel.
  - split.
    + intro Hnz.
      subst p.
      exists (Z.to_nat count).
      rewrite Z2Nat.id by lia.
      exact Hp.
    + intro Hpow.
      discriminate.
Qed.

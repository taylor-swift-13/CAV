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
From SimpleC.EE.CAV.verify_20260605_063617v_ex_allergies_score_count Require Import ex_allergies_score_count_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import ex_allergies_score_count.
Local Open Scope sac.

Definition allergies_bitsum (score : Z) : Z :=
  Z.b2z (Z.testbit score 0) +
  Z.b2z (Z.testbit score 1) +
  Z.b2z (Z.testbit score 2) +
  Z.b2z (Z.testbit score 3) +
  Z.b2z (Z.testbit score 4) +
  Z.b2z (Z.testbit score 5) +
  Z.b2z (Z.testbit score 6) +
  Z.b2z (Z.testbit score 7).

Lemma ex_allergies_score_count_spec_bits :
  forall score,
    0 <= score ->
    ex_allergies_score_count_spec score = allergies_bitsum score.
Proof.
  intros score Hscore.
  unfold ex_allergies_score_count_spec.
  simpl.
  assert (Hdiv0 : 0 <= score / 1).
  { rewrite Z.div_1_r. exact Hscore. }
  assert (Hdiv1 : 0 <= score / Z.pow_pos 2 1) by (apply Z.div_pos; [exact Hscore | lia]).
  assert (Hdiv2 : 0 <= score / Z.pow_pos 2 2) by (apply Z.div_pos; [exact Hscore | lia]).
  assert (Hdiv3 : 0 <= score / Z.pow_pos 2 3) by (apply Z.div_pos; [exact Hscore | lia]).
  assert (Hdiv4 : 0 <= score / Z.pow_pos 2 4) by (apply Z.div_pos; [exact Hscore | lia]).
  assert (Hdiv5 : 0 <= score / Z.pow_pos 2 5) by (apply Z.div_pos; [exact Hscore | lia]).
  assert (Hdiv6 : 0 <= score / Z.pow_pos 2 6) by (apply Z.div_pos; [exact Hscore | lia]).
  assert (Hdiv7 : 0 <= score / Z.pow_pos 2 7) by (apply Z.div_pos; [exact Hscore | lia]).
  rewrite (Z.rem_mod_nonneg (score / 1) 2 Hdiv0 ltac:(lia)).
  rewrite (Z.rem_mod_nonneg (score / Z.pow_pos 2 1) 2 Hdiv1 ltac:(lia)).
  rewrite (Z.rem_mod_nonneg (score / Z.pow_pos 2 2) 2 Hdiv2 ltac:(lia)).
  rewrite (Z.rem_mod_nonneg (score / Z.pow_pos 2 3) 2 Hdiv3 ltac:(lia)).
  rewrite (Z.rem_mod_nonneg (score / Z.pow_pos 2 4) 2 Hdiv4 ltac:(lia)).
  rewrite (Z.rem_mod_nonneg (score / Z.pow_pos 2 5) 2 Hdiv5 ltac:(lia)).
  rewrite (Z.rem_mod_nonneg (score / Z.pow_pos 2 6) 2 Hdiv6 ltac:(lia)).
  rewrite (Z.rem_mod_nonneg (score / Z.pow_pos 2 7) 2 Hdiv7 ltac:(lia)).
  rewrite Z.div_1_r.
  unfold allergies_bitsum.
  rewrite Z.bit0_mod.
  repeat rewrite Z.testbit_spec' by lia.
  reflexivity.
Qed.

Lemma land_low_mask_mod :
  forall score n,
    0 <= n ->
    Z.land score (Z.shiftl 1 n - 1) = score mod 2 ^ n.
Proof.
  intros score n Hn.
  rewrite Z.shiftl_1_l.
  replace (2 ^ n - 1) with (Z.ones n).
  2:{ rewrite Z.ones_equiv. lia. }
  apply Z.land_ones; lia.
Qed.

Lemma signed_last_nbits_shiftl_eq :
  forall i,
    0 <= i ->
    i < 31 ->
    signed_last_nbits (Z.shiftl 1 i) 32 = Z.shiftl 1 i.
Proof.
  intros i Hi0 Hi31.
  rewrite Z.shiftl_1_l.
  apply IntLib.signed_last_nbits_eq; [lia|].
  split.
  - assert (0 < 2 ^ i) by (apply Z.pow_pos_nonneg; lia).
    lia.
  - assert (2 ^ i < 2 ^ 31).
    { apply Z.pow_lt_mono_r; lia. }
    lia.
Qed.

Lemma land_single_bit_nonzero_testbit :
  forall score i,
    0 <= i ->
    Z.land score (2 ^ i) <> 0 ->
    Z.testbit score i = true.
Proof.
  intros score i Hi Hnz.
  destruct (Z.testbit score i) eqn:Hbit; [reflexivity|].
  exfalso.
  apply Hnz.
  apply Z.bits_inj_0.
  intros n.
  rewrite Z.land_spec.
  rewrite Z.pow2_bits_eqb by lia.
  destruct (i =? n) eqn:Heq.
  - apply Z.eqb_eq in Heq. subst n. rewrite Hbit. reflexivity.
  - destruct (Z.testbit score n); reflexivity.
Qed.

Lemma land_single_bit_zero_testbit :
  forall score i,
    0 <= i ->
    Z.land score (2 ^ i) = 0 ->
    Z.testbit score i = false.
Proof.
  intros score i Hi Hz.
  assert (Hbit0 : Z.testbit (Z.land score (2 ^ i)) i = false).
  { rewrite Hz. apply Z.bits_0. }
  rewrite Z.land_spec in Hbit0.
  rewrite Z.pow2_bits_eqb in Hbit0 by lia.
  rewrite Z.eqb_refl in Hbit0.
  destruct (Z.testbit score i); [discriminate|reflexivity].
Qed.

Lemma ex_allergies_score_count_prefix_step :
  forall score i,
    0 <= score ->
    0 <= i < 8 ->
    ex_allergies_score_count_spec (Z.land score (Z.shiftl 1 (i + 1) - 1)) =
    ex_allergies_score_count_spec (Z.land score (Z.shiftl 1 i - 1)) +
    Z.b2z (Z.testbit score i).
Proof.
  intros score i Hscore Hi.
  assert (Hi_cases :
    i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct Hi_cases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | -> ]]]]]]];
  repeat rewrite ex_allergies_score_count_spec_bits by
      (rewrite land_low_mask_mod by lia; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia);
  repeat rewrite land_low_mask_mod by lia;
  unfold allergies_bitsum;
  repeat rewrite Z.testbit_mod_pow2 by lia;
  simpl; lia.
Qed.

Lemma ex_allergies_score_count_prefix_full :
  forall score,
    0 <= score ->
    ex_allergies_score_count_spec (Z.land score (Z.shiftl 1 8 - 1)) =
    ex_allergies_score_count_spec score.
Proof.
  intros score Hscore.
  rewrite ex_allergies_score_count_spec_bits by
      (rewrite land_low_mask_mod by lia; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  rewrite ex_allergies_score_count_spec_bits by exact Hscore.
  rewrite land_low_mask_mod by lia.
  unfold allergies_bitsum.
  repeat rewrite Z.testbit_mod_pow2 by lia.
  simpl; lia.
Qed.

Lemma ex_allergies_score_count_spec_le_8 :
  forall score,
    ex_allergies_score_count_spec score <= 8.
Proof.
  intros score.
  unfold ex_allergies_score_count_spec.
  simpl.
  assert (H0 : Z.rem (score / 1) 2 <= 1).
  { pose proof (Z.rem_bound_abs (score / 1) 2 ltac:(lia)). lia. }
  assert (H1 : Z.rem (score / Z.pow_pos 2 1) 2 <= 1).
  { pose proof (Z.rem_bound_abs (score / Z.pow_pos 2 1) 2 ltac:(lia)). lia. }
  assert (H2 : Z.rem (score / Z.pow_pos 2 2) 2 <= 1).
  { pose proof (Z.rem_bound_abs (score / Z.pow_pos 2 2) 2 ltac:(lia)). lia. }
  assert (H3 : Z.rem (score / Z.pow_pos 2 3) 2 <= 1).
  { pose proof (Z.rem_bound_abs (score / Z.pow_pos 2 3) 2 ltac:(lia)). lia. }
  assert (H4 : Z.rem (score / Z.pow_pos 2 4) 2 <= 1).
  { pose proof (Z.rem_bound_abs (score / Z.pow_pos 2 4) 2 ltac:(lia)). lia. }
  assert (H5 : Z.rem (score / Z.pow_pos 2 5) 2 <= 1).
  { pose proof (Z.rem_bound_abs (score / Z.pow_pos 2 5) 2 ltac:(lia)). lia. }
  assert (H6 : Z.rem (score / Z.pow_pos 2 6) 2 <= 1).
  { pose proof (Z.rem_bound_abs (score / Z.pow_pos 2 6) 2 ltac:(lia)). lia. }
  assert (H7 : Z.rem (score / Z.pow_pos 2 7) 2 <= 1).
  { pose proof (Z.rem_bound_abs (score / Z.pow_pos 2 7) 2 ltac:(lia)). lia. }
  lia.
Qed.

Lemma proof_of_ex_allergies_score_count_safety_wit_4 : ex_allergies_score_count_safety_wit_4.
Proof.
  pre_process.
  entailer!.
  all: pose proof (IntLib.signed_Lastnbits_range (1 * 2 ^ i) 32) as Hrange.
  all: assert (32 > 0) by lia.
  all: specialize (Hrange H7).
  all: destruct Hrange as [Hlow Hhigh].
  all: lia.
Qed.

Lemma proof_of_ex_allergies_score_count_entail_wit_1 : ex_allergies_score_count_entail_wit_1.
Proof.
  pre_process.
  rewrite Z.shiftl_1_l.
  replace (2 ^ 0 - 1) with 0 by reflexivity.
  rewrite Z.land_0_r.
  unfold ex_allergies_score_count_spec.
  simpl.
  entailer!.
Qed.

Lemma proof_of_ex_allergies_score_count_entail_wit_2_1 : ex_allergies_score_count_entail_wit_2_1.
Proof.
  pre_process.
  entailer!.
  assert (Hshift :
    signed_last_nbits (Z.shiftl 1 i) 32 = Z.shiftl 1 i).
  { apply signed_last_nbits_shiftl_eq; lia. }
  assert (Hbit : Z.testbit score_pre i = true).
  { rewrite Hshift in H.
    rewrite Z.shiftl_1_l in H.
    apply land_single_bit_nonzero_testbit; lia.
  }
  rewrite H5.
  rewrite ex_allergies_score_count_prefix_step by lia.
  rewrite Hbit.
  simpl.
  ring_simplify.
  reflexivity.
Qed.

Lemma proof_of_ex_allergies_score_count_entail_wit_2_2 : ex_allergies_score_count_entail_wit_2_2.
Proof.
  pre_process.
  entailer!.
  assert (Hshift :
    signed_last_nbits (Z.shiftl 1 i) 32 = Z.shiftl 1 i).
  { apply signed_last_nbits_shiftl_eq; lia. }
  assert (Hbit : Z.testbit score_pre i = false).
  { rewrite Hshift in H.
    rewrite Z.shiftl_1_l in H.
    apply land_single_bit_zero_testbit; lia.
  }
  rewrite H5.
  rewrite ex_allergies_score_count_prefix_step by lia.
  rewrite Hbit.
  simpl.
  ring_simplify.
  reflexivity.
Qed.

Lemma proof_of_ex_allergies_score_count_entail_wit_3 : ex_allergies_score_count_entail_wit_3.
Proof.
  pre_process.
  entailer!.
  assert (i = 8) by lia.
  subst i.
  match goal with
  | Hcount : count = ex_allergies_score_count_spec (Z.land score_pre (Z.shiftl 1 8 - 1)) |- _ =>
      rewrite Hcount
  end.
  apply ex_allergies_score_count_prefix_full; lia.
Qed.

Lemma proof_of_ex_allergies_score_count_return_wit_1 : ex_allergies_score_count_return_wit_1.
Proof.
  pre_process.
  entailer!.
  rewrite H1.
  apply ex_allergies_score_count_spec_le_8.
Qed.

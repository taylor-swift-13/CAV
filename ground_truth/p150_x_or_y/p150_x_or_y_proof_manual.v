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
From SimpleC.EE Require Import p150_x_or_y_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Arith.
Require Import ZArith.
Require Import Coq.ZArith.Znumtheory.

Import naive_C_Rules.
Require Import p150_x_or_y.
Local Open Scope sac.
Require Import Coq.micromega.Lia.

Local Open Scope list_scope.

(* Proof helpers moved from p150_x_or_y.v so public contract files expose definitions only. *)

Lemma problem_150_spec_prime :
  forall n x y : Z,
  prime n ->
  problem_150_spec n x y x.
Proof.
  intros n x y Hp.
  unfold problem_150_spec.
  split; intro H.
  - reflexivity.
  - contradiction.
Qed.
Lemma problem_150_spec_not_prime :
  forall n x y : Z,
  ~ prime n ->
  problem_150_spec n x y y.
Proof.
  intros n x y Hnp.
  unfold problem_150_spec.
  split; intro H.
  - contradiction.
  - reflexivity.
Qed.
Lemma composite_has_small_prime_divisor :
  forall n : Z,
  2 <= n ->
  ~ prime n ->
  exists p : Z, prime p /\ Z.divide p n /\ p * p <= n.
Proof.
  refine (well_founded_induction_type (Z.lt_wf 1)
    (fun n => 2 <= n -> ~ prime n -> exists p, prime p /\ Z.divide p n /\ p * p <= n) _).
  intros n IH Hn2 Hn_not_prime.
  assert (Hn_gt1 : 1 < n) by lia.
  destruct (not_prime_divide n Hn_gt1 Hn_not_prime) as [d [[Hd_gt1 Hd_lt_n] Hd_div_n]].
  destruct Hd_div_n as [k Hn_eq].
  assert (Hd_pos : 0 < d) by lia.
  assert (Hk_pos : 0 < k) by (subst n; nia).
  assert (Hk_gt1 : 1 < k) by (subst n; nia).
  set (m := Z.min d k).
  assert (Hm_lt_n : m < n).
  {
    unfold m.
    destruct (Z_le_gt_dec d k) as [Hdk|Hdk].
    - rewrite Z.min_l by lia; lia.
    - rewrite Z.min_r by lia; lia.
  }
  assert (Hm_gt1 : 1 < m).
  {
    unfold m.
    destruct (Z_le_gt_dec d k) as [Hdk|Hdk].
    - rewrite Z.min_l by lia; lia.
    - rewrite Z.min_r by lia; lia.
  }
  assert (Hm_div_n : Z.divide m n).
  {
    unfold m.
    destruct (Z_le_gt_dec d k) as [Hdk|Hdk].
    - rewrite Z.min_l by lia. exists k. exact Hn_eq.
    - rewrite Z.min_r by lia. exists d. subst n. ring.
  }
  destruct (prime_dec m) as [Hm_prime|Hm_not_prime].
  - exists m. split; [exact Hm_prime|].
    split; [exact Hm_div_n|].
    unfold m.
    destruct (Z_le_gt_dec d k) as [Hdk|Hdk].
    + rewrite Z.min_l by lia. subst n. nia.
    + rewrite Z.min_r by lia. subst n. nia.
  - specialize (IH m).
    assert (Hm_range : 1 <= m < n) by lia.
    specialize (IH Hm_range).
    assert (Hm_ge2 : 2 <= m) by lia.
    specialize (IH Hm_ge2 Hm_not_prime).
    destruct IH as [p [Hp_prime [Hp_div_m Hp_sq_le_m]]].
    exists p. split; [exact Hp_prime|].
    split.
    + eapply Z.divide_trans; eauto.
    + lia.
Qed.
Lemma prime_of_no_divisors_upto_sqrt :
  forall n i : Z,
  2 <= n ->
  2 <= i ->
  i * i > n ->
  (forall k : Z, 2 <= k /\ k < i -> Z.rem n k <> 0) ->
  prime n.
Proof.
  intros n i Hn2 Hi2 Hexit Hnodiv.
  destruct (prime_dec n) as [Hp|Hnp]; [exact Hp|].
  exfalso.
  destruct (composite_has_small_prime_divisor n Hn2 Hnp) as [p [Hp_prime [Hp_div_n Hp_sq_le_n]]].
  assert (Hp_ge2 : 2 <= p) by (apply prime_ge_2; exact Hp_prime).
  assert (Hp_lt_i : p < i).
  {
    apply Z.nle_gt; intro Hp_ge_i.
    assert (Hi_sq_le_p_sq : i * i <= p * p) by nia.
    lia.
  }
  assert (Hprem0 : Z.rem n p = 0).
  {
    pose proof (Z.rem_divide n p ltac:(lia)) as Hiff.
    apply (proj2 Hiff).
    exact Hp_div_n.
  }
  specialize (Hnodiv p (conj Hp_ge2 Hp_lt_i)).
  contradiction.
Qed.
Lemma div_square_lt_from_exit :
  forall n i : Z,
  2 <= i ->
  i > n / i ->
  n < i * i.
Proof.
  intros n i Hi2 Hexit.
  assert (Hi_pos : 0 < i) by lia.
  pose proof (Z.div_mod n i (not_eq_sym (Z.lt_neq _ _ Hi_pos))) as Hmod.
  assert (Hr_bound : 0 <= n mod i < i) by (apply Z.mod_pos_bound; lia).
  destruct Hr_bound as [_ Hr_lt].
  nia.
Qed.
Lemma square_le_from_loop_guard :
  forall n i : Z,
  2 <= i ->
  i <= n / i ->
  i * i <= n.
Proof.
  intros n i Hi2 Hguard.
  assert (Hi_pos : 0 < i) by lia.
  pose proof (Z.div_mod n i (not_eq_sym (Z.lt_neq _ _ Hi_pos))) as Hmod.
  assert (Hr_bound : 0 <= n mod i < i) by (apply Z.mod_pos_bound; lia).
  destruct Hr_bound as [Hr_nonneg _].
  nia.
Qed.
Lemma not_prime_of_small_divisor :
  forall n d : Z,
  2 <= n ->
  2 <= d ->
  d < n ->
  Z.rem n d = 0 ->
  ~ prime n.
Proof.
  intros n d Hn2 Hd2 Hdlt Hrem Hp.
  assert (Hd_div_n : Z.divide d n).
  {
    pose proof (Z.rem_divide n d ltac:(lia)) as Hiff.
    apply (proj1 Hiff).
    exact Hrem.
  }
  destruct (prime_divisors n Hp d Hd_div_n) as [Hd|[Hd|[Hd|Hd]]]; lia.
Qed.


Lemma proof_of_p150_x_or_y_safety_wit_9 : p150_x_or_y_safety_wit_9.
Proof.
	unfold p150_x_or_y_safety_wit_9.
	intros.
	Intros.
	entailer!.
	assert (Hquot : n_pre ÷ i = n_pre / i) by (apply Z.quot_div_nonneg; lia).
	rewrite Hquot in H0.
	assert (Hi_sq : i * i <= n_pre).
	{ apply square_le_from_loop_guard; lia. }
	nia.
Qed. 

Lemma proof_of_p150_x_or_y_safety_wit_10 : p150_x_or_y_safety_wit_10.
Proof.
	unfold p150_x_or_y_safety_wit_10.
	intros.
	Intros.
	entailer!.
	assert (Hquot : n_pre ÷ i = n_pre / i) by (apply Z.quot_div_nonneg; lia).
	rewrite Hquot in H0.
	assert (Hi_sq : i * i <= n_pre).
	{ apply square_le_from_loop_guard; lia. }
	nia.
Qed. 

Lemma proof_of_p150_x_or_y_entail_wit_1 : p150_x_or_y_entail_wit_1.
Proof.
	unfold p150_x_or_y_entail_wit_1.
	intros.
	Intros.
	entailer!.
Qed. 

Lemma proof_of_p150_x_or_y_entail_wit_2_1 : p150_x_or_y_entail_wit_2_1.
Proof.
	unfold p150_x_or_y_entail_wit_2_1.
	intros.
	Intros.
	entailer!.
	Focus 1.
	intros.
	exists i.
	repeat split; lia.
	Focus 1.
	assert (Hquot : n_pre ÷ i = n_pre / i) by (apply Z.quot_div_nonneg; lia).
	rewrite Hquot in H0.
	assert (Hi_sq : i * i <= n_pre) by (apply square_le_from_loop_guard; lia).
	nia.
Qed. 

Lemma proof_of_p150_x_or_y_entail_wit_2_2 : p150_x_or_y_entail_wit_2_2.
Proof.
	unfold p150_x_or_y_entail_wit_2_2.
	intros.
	Intros.
	entailer!.
	Focus 1.
	intros.
	specialize (H4 H12).
	destruct H4 as [k [[Hk2 Hklt] Hkdiv]].
	exists k.
	lia.
	Focus 1.
	intros.
	assert (k < i \/ k = i) by lia.
	destruct H14 as [Hlt|Heq]; [apply (H3 H12); lia | subst k; exact H].
	Focus 1.
	assert (Hquot : n_pre ÷ i = n_pre / i) by (apply Z.quot_div_nonneg; lia).
	rewrite Hquot in H0.
	assert (Hi_sq : i * i <= n_pre) by (apply square_le_from_loop_guard; lia).
	nia.
Qed. 

Lemma proof_of_p150_x_or_y_return_wit_1 : p150_x_or_y_return_wit_1.
Proof.
  unfold p150_x_or_y_return_wit_1.
  intros.
  Intros.
  entailer!.
  apply problem_150_spec_not_prime; try lia.
  specialize (H3 H11).
  destruct H3 as [k [[Hk2 Hklt] Hkdiv]].
  eapply (not_prime_of_small_divisor n_pre k); eauto.
  lia.
Qed. 

Lemma proof_of_p150_x_or_y_return_wit_2 : p150_x_or_y_return_wit_2.
Proof.
  unfold p150_x_or_y_return_wit_2.
  intros.
  Intros.
  entailer!.
  apply problem_150_spec_prime; try lia.
  assert (Hquot : n_pre ÷ i = n_pre / i) by (apply Z.quot_div_nonneg; lia).
  rewrite Hquot in H.
  apply prime_of_no_divisors_upto_sqrt with (i := i); try lia.
  - pose proof (div_square_lt_from_exit n_pre i H0 H) as Hlt.
    lia.
  - intros k Hk.
    apply (H2 H11 k Hk).
Qed. 

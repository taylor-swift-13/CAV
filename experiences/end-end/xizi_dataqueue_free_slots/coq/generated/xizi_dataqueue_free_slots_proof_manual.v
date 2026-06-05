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
From SimpleC.EE.CAV.verify_20260603_000130v_xizi_dataqueue_free_slots Require Import xizi_dataqueue_free_slots_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma free_slots_range :
  forall max_len_pre rear_pre front_pre : Z,
    1 < max_len_pre ->
    0 <= front_pre < max_len_pre ->
    0 <= rear_pre < max_len_pre ->
    0 <=
      max_len_pre - 1 - ((rear_pre - front_pre + max_len_pre) % ( max_len_pre )) <
      max_len_pre.
Proof.
  intros.
  assert (0 < max_len_pre) by lia.
  assert (0 <= rear_pre - front_pre + max_len_pre) by lia.
  pose proof (Z.rem_bound_pos (rear_pre - front_pre + max_len_pre) max_len_pre H3 H2).
  lia.
Qed.

Lemma free_slots_case_front_le_rear :
  forall max_len_pre rear_pre front_pre : Z,
    1 < max_len_pre ->
    0 <= front_pre < max_len_pre ->
    0 <= rear_pre < max_len_pre ->
    front_pre <= rear_pre ->
    max_len_pre - 1 - ((rear_pre - front_pre + max_len_pre) % ( max_len_pre )) =
    max_len_pre - 1 - (rear_pre - front_pre).
Proof.
  intros.
  assert (0 <= rear_pre - front_pre < max_len_pre) by lia.
  assert (0 <= rear_pre - front_pre + max_len_pre) by lia.
  rewrite Z.rem_mod_nonneg by lia.
  replace (rear_pre - front_pre + max_len_pre)
    with ((rear_pre - front_pre) + 1 * max_len_pre) by lia.
  rewrite Z.mod_add by lia.
  rewrite Z.mod_small by lia.
  lia.
Qed.

Lemma free_slots_case_rear_lt_front :
  forall max_len_pre rear_pre front_pre : Z,
    1 < max_len_pre ->
    0 <= front_pre < max_len_pre ->
    0 <= rear_pre < max_len_pre ->
    rear_pre < front_pre ->
    max_len_pre - 1 - ((rear_pre - front_pre + max_len_pre) % ( max_len_pre )) =
    front_pre - rear_pre - 1.
Proof.
  intros.
  assert (0 <= rear_pre - front_pre + max_len_pre < max_len_pre) by lia.
  rewrite Z.rem_mod_nonneg by lia.
  rewrite Z.mod_small by lia.
  lia.
Qed.

Lemma free_slots_nonneg :
  forall max_len_pre rear_pre front_pre : Z,
    1 < max_len_pre ->
    0 <= front_pre < max_len_pre ->
    0 <= rear_pre < max_len_pre ->
    0 <=
      max_len_pre - 1 - ((rear_pre - front_pre + max_len_pre) % ( max_len_pre )).
Proof.
  intros.
  pose proof (free_slots_range max_len_pre rear_pre front_pre H H0 H1) as Hrange.
  lia.
Qed.

Lemma free_slots_below_max :
  forall max_len_pre rear_pre front_pre : Z,
    1 < max_len_pre ->
    0 <= front_pre < max_len_pre ->
    0 <= rear_pre < max_len_pre ->
    max_len_pre - 1 - ((rear_pre - front_pre + max_len_pre) % ( max_len_pre )) <
    max_len_pre.
Proof.
  intros.
  pose proof (free_slots_range max_len_pre rear_pre front_pre H H0 H1) as Hrange.
  lia.
Qed.

Lemma free_slots_sint_lower :
  forall max_len_pre rear_pre front_pre : Z,
    1 < max_len_pre ->
    0 <= front_pre < max_len_pre ->
    0 <= rear_pre < max_len_pre ->
    INT_MIN <=
      max_len_pre - 1 - ((rear_pre - front_pre + max_len_pre) % ( max_len_pre )).
Proof.
  intros.
  pose proof (free_slots_nonneg max_len_pre rear_pre front_pre H H0 H1).
  lia.
Qed.

Lemma free_slots_sint_upper :
  forall max_len_pre rear_pre front_pre : Z,
    1 < max_len_pre ->
    max_len_pre <= 1073741824 ->
    0 <= front_pre < max_len_pre ->
    0 <= rear_pre < max_len_pre ->
    max_len_pre - 1 - ((rear_pre - front_pre + max_len_pre) % ( max_len_pre )) <=
    INT_MAX.
Proof.
  intros.
  pose proof (free_slots_below_max max_len_pre rear_pre front_pre H H1 H2).
  lia.
Qed.

Lemma proof_of_xizi_dataqueue_free_slots_safety_wit_4 : xizi_dataqueue_free_slots_safety_wit_4.
Proof.
  pre_process.
  entailer!.
  - pose proof (free_slots_sint_lower max_len_pre rear_pre front_pre H (conj H1 H2) (conj H3 H4)) as Hbound.
    exact Hbound.
  - pose proof (free_slots_sint_upper max_len_pre rear_pre front_pre H H0 (conj H1 H2) (conj H3 H4)) as Hbound.
    exact Hbound.
Qed.

Lemma proof_of_xizi_dataqueue_free_slots_return_wit_1 : xizi_dataqueue_free_slots_return_wit_1.
Proof.
  pre_process.
  entailer!.
  - intros Hlt.
    apply free_slots_case_rear_lt_front; try lia.
  - intros Hle.
    apply free_slots_case_front_le_rear; try lia.
  - apply free_slots_below_max; try lia.
  - apply free_slots_nonneg; try lia.
Qed.

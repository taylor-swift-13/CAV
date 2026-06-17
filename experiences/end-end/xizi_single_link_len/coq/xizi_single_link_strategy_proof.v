Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import xizi_single_link_lib.
Require Import xizi_single_link_strategy_goal.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma xizi_single_link_strategy301_correctness : xizi_single_link_strategy301.
Proof.
  pre_process_default.
  simpl xizi_sll.
  entailer!.
Qed.

Lemma xizi_single_link_strategy302_correctness : xizi_single_link_strategy302.
Proof.
  pre_process_default.
  simpl xizi_sll.
  entailer!.
Qed.

Lemma xizi_single_link_strategy303_correctness : xizi_single_link_strategy303.
Proof.
  pre_process_default.
  entailer!.
  subst.
  simpl xizi_sll.
  entailer!.
Qed.

Lemma xizi_single_link_strategy304_correctness : xizi_single_link_strategy304.
Proof.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  Intros.
  assert (p <> 0) by (destruct H; congruence).
  sep_apply xizi_sll_not_zero; [ | tauto ].
  Intros d q l0.
  Exists d q l0.
  rewrite <- logic_equiv_coq_prop_or.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma xizi_single_link_strategy305_correctness : xizi_single_link_strategy305.
Proof.
  pre_process_default.
  unfold xizi_sll_head.
  Intros q.
  Exists q.
  entailer!.
  rewrite <- derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma xizi_single_link_strategy306_correctness : xizi_single_link_strategy306.
Proof.
  pre_process_default.
  unfold xizi_sll_head.
  Exists q.
  entailer!.
Qed.

Lemma xizi_single_link_strategy307_correctness : xizi_single_link_strategy307.
Proof.
  pre_process_default.
  Intros.
  subst.
  simpl xizi_sllseg.
  entailer!.
Qed.

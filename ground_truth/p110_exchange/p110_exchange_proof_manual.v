Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p110_exchange Require Import p110_exchange_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p110_exchange.
Local Open Scope sac.

Ltac exchange_base :=
  pre_process;
  subst;
  entailer!;
  try rewrite count_even_upto_0;
  try lia.

Ltac exchange_step_even :=
  pre_process;
  subst;
  entailer!;
  match goal with
  | Hrem : Z.rem (Znth ?i ?l 0) 2 = 0 |- _ =>
      rewrite (count_even_upto_step_rem_even i l) by lia;
      lia
  end.

Ltac exchange_step_odd :=
  pre_process;
  subst;
  entailer!;
  match goal with
  | Hrem : Z.rem (Znth ?i ?l 0) 2 <> 0 |- _ =>
      rewrite (count_even_upto_step_rem_not_even i l) by lia;
      lia
  end.

Lemma proof_of_p110_exchange_entail_wit_1 : p110_exchange_entail_wit_1.
Proof.
  unfold p110_exchange_entail_wit_1.
  intros.
  exchange_base.
Qed. 

Lemma proof_of_p110_exchange_entail_wit_2_1 : p110_exchange_entail_wit_2_1.
Proof.
  unfold p110_exchange_entail_wit_2_1.
  intros.
  exchange_step_even.
Qed. 

Lemma proof_of_p110_exchange_entail_wit_2_2 : p110_exchange_entail_wit_2_2.
Proof.
  unfold p110_exchange_entail_wit_2_2.
  intros.
  exchange_step_odd.
Qed. 

Lemma proof_of_p110_exchange_entail_wit_3 : p110_exchange_entail_wit_3.
Proof.
  unfold p110_exchange_entail_wit_3.
  intros.
  pre_process.
  subst.
  assert (i = Zlength l1) by lia.
  subst i.
  entailer!.
Qed.

Lemma proof_of_p110_exchange_entail_wit_4 : p110_exchange_entail_wit_4.
Proof.
  unfold p110_exchange_entail_wit_4.
  intros.
  exchange_base.
Qed. 

Lemma proof_of_p110_exchange_entail_wit_5_1 : p110_exchange_entail_wit_5_1.
Proof.
  unfold p110_exchange_entail_wit_5_1.
  intros.
  exchange_step_even.
Qed. 

Lemma proof_of_p110_exchange_entail_wit_5_2 : p110_exchange_entail_wit_5_2.
Proof.
  unfold p110_exchange_entail_wit_5_2.
  intros.
  exchange_step_odd.
Qed. 

Lemma proof_of_p110_exchange_return_wit_1 : p110_exchange_return_wit_1.
Proof.
  unfold p110_exchange_return_wit_1.
  intros.
  pre_process.
  subst.
  entailer!.
  assert (i = Zlength l2) by lia.
  subst i.
  rewrite (count_even_upto_full l1 (Zlength l1) eq_refl) in *.
  rewrite (count_even_upto_full l2 (Zlength l2) eq_refl) in *.
  eapply problem_110_spec_false with (total_even := count_even_list l1 + count_even_list l2); eauto; lia.
Qed. 

Lemma proof_of_p110_exchange_return_wit_2 : p110_exchange_return_wit_2.
Proof.
  unfold p110_exchange_return_wit_2.
  intros.
  pre_process.
  subst.
  entailer!.
  assert (i = Zlength l2) by lia.
  subst i.
  rewrite (count_even_upto_full l1 (Zlength l1) eq_refl) in *.
  rewrite (count_even_upto_full l2 (Zlength l2) eq_refl) in *.
  eapply problem_110_spec_true with (total_even := count_even_list l1 + count_even_list l2); eauto; lia.
Qed. 

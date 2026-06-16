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
From SimpleC.EE.CAV.verify_20260608_1701043326_p046_fib4 Require Import p046_fib4_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p046_fib4.
Local Open Scope sac.

Lemma proof_of_p046_fib4_safety_wit_14 : p046_fib4_safety_wit_14.
Proof.
  unfold p046_fib4_safety_wit_14.
  intros.
  pre_process.
  Intros.
  subst.
  entailer!.
  try lia.
Qed.

Lemma proof_of_p046_fib4_safety_wit_15 : p046_fib4_safety_wit_15.
Proof.
  unfold p046_fib4_safety_wit_15.
  intros.
  pre_process.
  Intros.
  subst.
  entailer!.
  try lia.
Qed.

Lemma proof_of_p046_fib4_safety_wit_16 : p046_fib4_safety_wit_16.
Proof.
  unfold p046_fib4_safety_wit_16.
  intros.
  pre_process.
  Intros.
  subst.
  entailer!.
  try lia.
Qed.

Lemma proof_of_p046_fib4_safety_wit_17 : p046_fib4_safety_wit_17.
Proof.
  unfold p046_fib4_safety_wit_17.
  intros.
  pre_process.
  Intros.
  subst.
  entailer!.
  try lia.
Qed.

Lemma proof_of_p046_fib4_entail_wit_1 : p046_fib4_entail_wit_1.
Proof.
  unfold p046_fib4_entail_wit_1.
  intros.
  pre_process.
  Intros.
  subst.
  cbv [fib4 fib4_fuel].
  entailer!.
  try lia.
Qed.

Lemma proof_of_p046_fib4_entail_wit_2 : p046_fib4_entail_wit_2.
Proof.
  unfold p046_fib4_entail_wit_2.
  intros.
  pre_process.
  Intros.
  subst.
  entailer!.
  try lia.
Qed.

Lemma proof_of_p046_fib4_return_wit_1 : p046_fib4_return_wit_1.
Proof.
  unfold p046_fib4_return_wit_1.
  intros.
  pre_process.
  Intros.
  subst.
  entailer!.
  try lia.
Qed.

Lemma proof_of_p046_fib4_return_wit_2 : p046_fib4_return_wit_2.
Proof.
  unfold p046_fib4_return_wit_2.
  intros.
  pre_process.
  Intros.
  subst.
  cbv [fib4 fib4_fuel].
  entailer!.
  try lia.
Qed.

Lemma proof_of_p046_fib4_return_wit_3 : p046_fib4_return_wit_3.
Proof.
  unfold p046_fib4_return_wit_3.
  intros.
  pre_process.
  Intros.
  subst.
  cbv [fib4 fib4_fuel].
  entailer!.
  try lia.
Qed.

Lemma proof_of_p046_fib4_return_wit_4 : p046_fib4_return_wit_4.
Proof.
  unfold p046_fib4_return_wit_4.
  intros.
  pre_process.
  Intros.
  subst.
  cbv [fib4 fib4_fuel].
  entailer!.
  try lia.
Qed.

Lemma proof_of_p046_fib4_return_wit_5 : p046_fib4_return_wit_5.
Proof.
  unfold p046_fib4_return_wit_5.
  intros.
  pre_process.
  Intros.
  subst.
  cbv [fib4 fib4_fuel].
  entailer!.
  try lia.
Qed.

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
From SimpleC.EE.CAV.verify_20260604_105149_leap_year Require Import leap_year_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_leap_year_return_wit_4 : leap_year_return_wit_4.
Proof.
  pre_process; entailer!.
  intro H4.
  exfalso.
  apply H4.
  pose proof (Z.quot_rem year_pre 400 ltac:(lia)) as Hqr.
  assert (Heq : year_pre = 100 * (year_pre ÷ 400) * 4) by lia.
  rewrite Heq.
  apply Z.rem_mul. lia.
Qed.


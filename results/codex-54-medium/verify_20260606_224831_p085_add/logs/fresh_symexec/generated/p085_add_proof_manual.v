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
From SimpleC.EE.CAV.verify_20260606_224831_p085_add Require Import p085_add_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p085_add.
Local Open Scope sac.

Lemma proof_of_p085_add_safety_wit_14 : p085_add_safety_wit_14.
Proof. Admitted. 

Lemma proof_of_p085_add_entail_wit_1 : p085_add_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_p085_add_entail_wit_2_1 : p085_add_entail_wit_2_1.
Proof. Admitted. 

Lemma proof_of_p085_add_entail_wit_2_2 : p085_add_entail_wit_2_2.
Proof. Admitted. 

Lemma proof_of_p085_add_return_wit_1 : p085_add_return_wit_1.
Proof. Admitted. 


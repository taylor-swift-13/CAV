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
From SimpleC.EE.CAV.verify_20260605_080500v_ex_grains_square_value Require Import ex_grains_square_value_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import power_nonnegative.
Local Open Scope sac.

Lemma proof_of_ex_grains_square_value_safety_wit_1 : ex_grains_square_value_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_ex_grains_square_value_safety_wit_2 : ex_grains_square_value_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_ex_grains_square_value_safety_wit_4 : ex_grains_square_value_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_ex_grains_square_value_safety_wit_5 : ex_grains_square_value_safety_wit_5.
Proof. Admitted. 


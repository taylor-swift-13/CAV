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
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import power_nonnegative.
Local Open Scope sac.

(*----- Function ex_grains_square_value -----*)

Definition ex_grains_square_value_safety_wit_1 := 
forall (square_pre: Z) ,
  “ (1 <= square_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= (square_pre - 1 ))) -> (((INT_MIN) <= (power_nonnegative_z (2) (k))) /\ ((power_nonnegative_z (2) (k)) <= INT_MAX))) ”
  &&  ((( &( "value" ) )) # Int  |->_)
  **  ((( &( "square" ) )) # Int  |-> square_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ex_grains_square_value_safety_wit_2 := 
forall (square_pre: Z) ,
  “ (1 <= square_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= (square_pre - 1 ))) -> (((INT_MIN) <= (power_nonnegative_z (2) (k))) /\ ((power_nonnegative_z (2) (k)) <= INT_MAX))) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "value" ) )) # Int  |-> 1)
  **  ((( &( "square" ) )) # Int  |-> square_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ex_grains_square_value_safety_wit_3 := 
forall (square_pre: Z) (value: Z) (i: Z) ,
  “ (i < square_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= square_pre) ” 
  &&  “ (value = (power_nonnegative_z (2) ((i - 1 )))) ” 
  &&  “ (1 <= square_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= (square_pre - 1 ))) -> (((INT_MIN) <= (power_nonnegative_z (2) (k))) /\ ((power_nonnegative_z (2) (k)) <= INT_MAX))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "square" ) )) # Int  |-> square_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
|--
  “ ((value * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (value * 2 )) ”
.

Definition ex_grains_square_value_safety_wit_4 := 
forall (square_pre: Z) (value: Z) (i: Z) ,
  “ (i < square_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= square_pre) ” 
  &&  “ (value = (power_nonnegative_z (2) ((i - 1 )))) ” 
  &&  “ (1 <= square_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= (square_pre - 1 ))) -> (((INT_MIN) <= (power_nonnegative_z (2) (k))) /\ ((power_nonnegative_z (2) (k)) <= INT_MAX))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "square" ) )) # Int  |-> square_pre)
  **  ((( &( "value" ) )) # Int  |-> value)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition ex_grains_square_value_safety_wit_5 := 
forall (square_pre: Z) (value: Z) (i: Z) ,
  “ (i < square_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= square_pre) ” 
  &&  “ (value = (power_nonnegative_z (2) ((i - 1 )))) ” 
  &&  “ (1 <= square_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= (square_pre - 1 ))) -> (((INT_MIN) <= (power_nonnegative_z (2) (k))) /\ ((power_nonnegative_z (2) (k)) <= INT_MAX))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "square" ) )) # Int  |-> square_pre)
  **  ((( &( "value" ) )) # Int  |-> (value * 2 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition ex_grains_square_value_entail_wit_1 := 
forall (square_pre: Z) ,
  “ (1 <= square_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= (square_pre - 1 ))) -> (((INT_MIN) <= (power_nonnegative_z (2) (k))) /\ ((power_nonnegative_z (2) (k)) <= INT_MAX))) ”
  &&  emp
|--
  “ (1 <= 1) ” 
  &&  “ (1 <= square_pre) ” 
  &&  “ (1 = (power_nonnegative_z (2) ((1 - 1 )))) ” 
  &&  “ (1 <= square_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= (square_pre - 1 ))) -> (((INT_MIN) <= (power_nonnegative_z (2) (k))) /\ ((power_nonnegative_z (2) (k)) <= INT_MAX))) ”
  &&  emp
.

Definition ex_grains_square_value_entail_wit_2 := 
forall (square_pre: Z) (value: Z) (i: Z) ,
  “ (i < square_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= square_pre) ” 
  &&  “ (value = (power_nonnegative_z (2) ((i - 1 )))) ” 
  &&  “ (1 <= square_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= (square_pre - 1 ))) -> (((INT_MIN) <= (power_nonnegative_z (2) (k))) /\ ((power_nonnegative_z (2) (k)) <= INT_MAX))) ”
  &&  emp
|--
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= square_pre) ” 
  &&  “ ((value * 2 ) = (power_nonnegative_z (2) (((i + 1 ) - 1 )))) ” 
  &&  “ (1 <= square_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= (square_pre - 1 ))) -> (((INT_MIN) <= (power_nonnegative_z (2) (k))) /\ ((power_nonnegative_z (2) (k)) <= INT_MAX))) ”
  &&  emp
.

Definition ex_grains_square_value_return_wit_1 := 
forall (square_pre: Z) (value: Z) (i: Z) ,
  “ (i >= square_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= square_pre) ” 
  &&  “ (value = (power_nonnegative_z (2) ((i - 1 )))) ” 
  &&  “ (1 <= square_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k <= (square_pre - 1 ))) -> (((INT_MIN) <= (power_nonnegative_z (2) (k))) /\ ((power_nonnegative_z (2) (k)) <= INT_MAX))) ”
  &&  emp
|--
  “ (value = (power_nonnegative_z (2) ((square_pre - 1 )))) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_ex_grains_square_value_safety_wit_1 : ex_grains_square_value_safety_wit_1.
Axiom proof_of_ex_grains_square_value_safety_wit_2 : ex_grains_square_value_safety_wit_2.
Axiom proof_of_ex_grains_square_value_safety_wit_3 : ex_grains_square_value_safety_wit_3.
Axiom proof_of_ex_grains_square_value_safety_wit_4 : ex_grains_square_value_safety_wit_4.
Axiom proof_of_ex_grains_square_value_safety_wit_5 : ex_grains_square_value_safety_wit_5.
Axiom proof_of_ex_grains_square_value_entail_wit_1 : ex_grains_square_value_entail_wit_1.
Axiom proof_of_ex_grains_square_value_entail_wit_2 : ex_grains_square_value_entail_wit_2.
Axiom proof_of_ex_grains_square_value_return_wit_1 : ex_grains_square_value_return_wit_1.

End VC_Correct.

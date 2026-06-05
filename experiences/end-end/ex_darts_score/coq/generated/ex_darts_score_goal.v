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
Local Open Scope sac.

(*----- Function ex_darts_score -----*)

Definition ex_darts_score_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  “ ((-46340) <= x_pre) ” 
  &&  “ (x_pre <= 46340) ” 
  &&  “ ((-46340) <= y_pre) ” 
  &&  “ (y_pre <= 46340) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((x_pre * x_pre ) + (y_pre * y_pre ) )) ”
.

Definition ex_darts_score_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) ,
  “ ((-46340) <= x_pre) ” 
  &&  “ (x_pre <= 46340) ” 
  &&  “ ((-46340) <= y_pre) ” 
  &&  “ (y_pre <= 46340) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ ((y_pre * y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y_pre * y_pre )) ”
.

Definition ex_darts_score_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) ,
  “ ((-46340) <= x_pre) ” 
  &&  “ (x_pre <= 46340) ” 
  &&  “ ((-46340) <= y_pre) ” 
  &&  “ (y_pre <= 46340) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ ((x_pre * x_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre * x_pre )) ”
.

Definition ex_darts_score_safety_wit_4 := 
forall (y_pre: Z) (x_pre: Z) ,
  “ ((-46340) <= x_pre) ” 
  &&  “ (x_pre <= 46340) ” 
  &&  “ ((-46340) <= y_pre) ” 
  &&  “ (y_pre <= 46340) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> ((x_pre * x_pre ) + (y_pre * y_pre ) ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ex_darts_score_safety_wit_5 := 
forall (y_pre: Z) (x_pre: Z) ,
  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= 1) ” 
  &&  “ ((-46340) <= x_pre) ” 
  &&  “ (x_pre <= 46340) ” 
  &&  “ ((-46340) <= y_pre) ” 
  &&  “ (y_pre <= 46340) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> ((x_pre * x_pre ) + (y_pre * y_pre ) ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition ex_darts_score_safety_wit_6 := 
forall (y_pre: Z) (x_pre: Z) ,
  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) > 1) ” 
  &&  “ ((-46340) <= x_pre) ” 
  &&  “ (x_pre <= 46340) ” 
  &&  “ ((-46340) <= y_pre) ” 
  &&  “ (y_pre <= 46340) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> ((x_pre * x_pre ) + (y_pre * y_pre ) ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (25 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 25) ”
.

Definition ex_darts_score_safety_wit_7 := 
forall (y_pre: Z) (x_pre: Z) ,
  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= 25) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) > 1) ” 
  &&  “ ((-46340) <= x_pre) ” 
  &&  “ (x_pre <= 46340) ” 
  &&  “ ((-46340) <= y_pre) ” 
  &&  “ (y_pre <= 46340) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> ((x_pre * x_pre ) + (y_pre * y_pre ) ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition ex_darts_score_safety_wit_8 := 
forall (y_pre: Z) (x_pre: Z) ,
  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) > 25) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) > 1) ” 
  &&  “ ((-46340) <= x_pre) ” 
  &&  “ (x_pre <= 46340) ” 
  &&  “ ((-46340) <= y_pre) ” 
  &&  “ (y_pre <= 46340) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> ((x_pre * x_pre ) + (y_pre * y_pre ) ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition ex_darts_score_safety_wit_9 := 
forall (y_pre: Z) (x_pre: Z) ,
  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= 100) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) > 25) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) > 1) ” 
  &&  “ ((-46340) <= x_pre) ” 
  &&  “ (x_pre <= 46340) ” 
  &&  “ ((-46340) <= y_pre) ” 
  &&  “ (y_pre <= 46340) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> ((x_pre * x_pre ) + (y_pre * y_pre ) ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ex_darts_score_safety_wit_10 := 
forall (y_pre: Z) (x_pre: Z) ,
  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) > 100) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) > 25) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) > 1) ” 
  &&  “ ((-46340) <= x_pre) ” 
  &&  “ (x_pre <= 46340) ” 
  &&  “ ((-46340) <= y_pre) ” 
  &&  “ (y_pre <= 46340) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> ((x_pre * x_pre ) + (y_pre * y_pre ) ))
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ex_darts_score_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) > 100) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) > 25) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) > 1) ” 
  &&  “ ((-46340) <= x_pre) ” 
  &&  “ (x_pre <= 46340) ” 
  &&  “ ((-46340) <= y_pre) ” 
  &&  “ (y_pre <= 46340) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= INT_MAX) ”
  &&  emp
|--
  “ ((((x_pre * x_pre ) + (y_pre * y_pre ) ) <= 1) -> (0 = 10)) ” 
  &&  “ (((1 < ((x_pre * x_pre ) + (y_pre * y_pre ) )) /\ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= 25)) -> (0 = 5)) ” 
  &&  “ (((25 < ((x_pre * x_pre ) + (y_pre * y_pre ) )) /\ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= 100)) -> (0 = 1)) ” 
  &&  “ ((100 < ((x_pre * x_pre ) + (y_pre * y_pre ) )) -> (0 = 0)) ”
  &&  emp
.

Definition ex_darts_score_return_wit_2 := 
forall (y_pre: Z) (x_pre: Z) ,
  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= 100) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) > 25) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) > 1) ” 
  &&  “ ((-46340) <= x_pre) ” 
  &&  “ (x_pre <= 46340) ” 
  &&  “ ((-46340) <= y_pre) ” 
  &&  “ (y_pre <= 46340) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= INT_MAX) ”
  &&  emp
|--
  “ ((((x_pre * x_pre ) + (y_pre * y_pre ) ) <= 1) -> (1 = 10)) ” 
  &&  “ (((1 < ((x_pre * x_pre ) + (y_pre * y_pre ) )) /\ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= 25)) -> (1 = 5)) ” 
  &&  “ (((25 < ((x_pre * x_pre ) + (y_pre * y_pre ) )) /\ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= 100)) -> (1 = 1)) ” 
  &&  “ ((100 < ((x_pre * x_pre ) + (y_pre * y_pre ) )) -> (1 = 0)) ”
  &&  emp
.

Definition ex_darts_score_return_wit_3 := 
forall (y_pre: Z) (x_pre: Z) ,
  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= 25) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) > 1) ” 
  &&  “ ((-46340) <= x_pre) ” 
  &&  “ (x_pre <= 46340) ” 
  &&  “ ((-46340) <= y_pre) ” 
  &&  “ (y_pre <= 46340) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= INT_MAX) ”
  &&  emp
|--
  “ ((((x_pre * x_pre ) + (y_pre * y_pre ) ) <= 1) -> (5 = 10)) ” 
  &&  “ (((1 < ((x_pre * x_pre ) + (y_pre * y_pre ) )) /\ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= 25)) -> (5 = 5)) ” 
  &&  “ (((25 < ((x_pre * x_pre ) + (y_pre * y_pre ) )) /\ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= 100)) -> (5 = 1)) ” 
  &&  “ ((100 < ((x_pre * x_pre ) + (y_pre * y_pre ) )) -> (5 = 0)) ”
  &&  emp
.

Definition ex_darts_score_return_wit_4 := 
forall (y_pre: Z) (x_pre: Z) ,
  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= 1) ” 
  &&  “ ((-46340) <= x_pre) ” 
  &&  “ (x_pre <= 46340) ” 
  &&  “ ((-46340) <= y_pre) ” 
  &&  “ (y_pre <= 46340) ” 
  &&  “ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= INT_MAX) ”
  &&  emp
|--
  “ ((((x_pre * x_pre ) + (y_pre * y_pre ) ) <= 1) -> (10 = 10)) ” 
  &&  “ (((1 < ((x_pre * x_pre ) + (y_pre * y_pre ) )) /\ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= 25)) -> (10 = 5)) ” 
  &&  “ (((25 < ((x_pre * x_pre ) + (y_pre * y_pre ) )) /\ (((x_pre * x_pre ) + (y_pre * y_pre ) ) <= 100)) -> (10 = 1)) ” 
  &&  “ ((100 < ((x_pre * x_pre ) + (y_pre * y_pre ) )) -> (10 = 0)) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_ex_darts_score_safety_wit_1 : ex_darts_score_safety_wit_1.
Axiom proof_of_ex_darts_score_safety_wit_2 : ex_darts_score_safety_wit_2.
Axiom proof_of_ex_darts_score_safety_wit_3 : ex_darts_score_safety_wit_3.
Axiom proof_of_ex_darts_score_safety_wit_4 : ex_darts_score_safety_wit_4.
Axiom proof_of_ex_darts_score_safety_wit_5 : ex_darts_score_safety_wit_5.
Axiom proof_of_ex_darts_score_safety_wit_6 : ex_darts_score_safety_wit_6.
Axiom proof_of_ex_darts_score_safety_wit_7 : ex_darts_score_safety_wit_7.
Axiom proof_of_ex_darts_score_safety_wit_8 : ex_darts_score_safety_wit_8.
Axiom proof_of_ex_darts_score_safety_wit_9 : ex_darts_score_safety_wit_9.
Axiom proof_of_ex_darts_score_safety_wit_10 : ex_darts_score_safety_wit_10.
Axiom proof_of_ex_darts_score_return_wit_1 : ex_darts_score_return_wit_1.
Axiom proof_of_ex_darts_score_return_wit_2 : ex_darts_score_return_wit_2.
Axiom proof_of_ex_darts_score_return_wit_3 : ex_darts_score_return_wit_3.
Axiom proof_of_ex_darts_score_return_wit_4 : ex_darts_score_return_wit_4.

End VC_Correct.

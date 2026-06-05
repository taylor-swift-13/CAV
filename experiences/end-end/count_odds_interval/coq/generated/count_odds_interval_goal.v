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

(*----- Function count_odds_interval -----*)

Definition count_odds_interval_safety_wit_1 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
|--
  “ ((low_pre <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition count_odds_interval_safety_wit_2 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition count_odds_interval_safety_wit_3 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition count_odds_interval_safety_wit_4 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ ((low_pre % ( 2 ) ) = 0) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
|--
  “ ((high_pre <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition count_odds_interval_safety_wit_5 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ ((low_pre % ( 2 ) ) = 0) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition count_odds_interval_safety_wit_6 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ ((low_pre % ( 2 ) ) = 0) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition count_odds_interval_safety_wit_7 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ ((high_pre % ( 2 ) ) = 0) ” 
  &&  “ ((low_pre % ( 2 ) ) = 0) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
|--
  “ (((high_pre - low_pre ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition count_odds_interval_safety_wit_8 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ ((high_pre % ( 2 ) ) = 0) ” 
  &&  “ ((low_pre % ( 2 ) ) = 0) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
|--
  “ ((high_pre - low_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (high_pre - low_pre )) ”
.

Definition count_odds_interval_safety_wit_9 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ ((high_pre % ( 2 ) ) = 0) ” 
  &&  “ ((low_pre % ( 2 ) ) = 0) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition count_odds_interval_safety_wit_10 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ ((low_pre % ( 2 ) ) <> 0) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
|--
  “ ((((high_pre - low_pre ) ÷ 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((high_pre - low_pre ) ÷ 2 ) + 1 )) ”
.

Definition count_odds_interval_safety_wit_11 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ ((high_pre % ( 2 ) ) <> 0) ” 
  &&  “ ((low_pre % ( 2 ) ) = 0) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
|--
  “ ((((high_pre - low_pre ) ÷ 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((high_pre - low_pre ) ÷ 2 ) + 1 )) ”
.

Definition count_odds_interval_safety_wit_12 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ ((low_pre % ( 2 ) ) <> 0) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
|--
  “ (((high_pre - low_pre ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition count_odds_interval_safety_wit_13 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ ((high_pre % ( 2 ) ) <> 0) ” 
  &&  “ ((low_pre % ( 2 ) ) = 0) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
|--
  “ (((high_pre - low_pre ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition count_odds_interval_safety_wit_14 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ ((low_pre % ( 2 ) ) <> 0) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
|--
  “ ((high_pre - low_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (high_pre - low_pre )) ”
.

Definition count_odds_interval_safety_wit_15 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ ((high_pre % ( 2 ) ) <> 0) ” 
  &&  “ ((low_pre % ( 2 ) ) = 0) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
|--
  “ ((high_pre - low_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (high_pre - low_pre )) ”
.

Definition count_odds_interval_safety_wit_16 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ ((high_pre % ( 2 ) ) <> 0) ” 
  &&  “ ((low_pre % ( 2 ) ) = 0) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition count_odds_interval_safety_wit_17 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ ((low_pre % ( 2 ) ) <> 0) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition count_odds_interval_safety_wit_18 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ ((high_pre % ( 2 ) ) <> 0) ” 
  &&  “ ((low_pre % ( 2 ) ) = 0) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition count_odds_interval_safety_wit_19 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ ((low_pre % ( 2 ) ) <> 0) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition count_odds_interval_return_wit_1 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ ((low_pre % ( 2 ) ) <> 0) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  emp
|--
  “ ((((low_pre % ( 2 ) ) = 0) /\ ((high_pre % ( 2 ) ) = 0)) -> ((((high_pre - low_pre ) ÷ 2 ) + 1 ) = ((high_pre - low_pre ) ÷ 2 ))) ” 
  &&  “ ((((low_pre % ( 2 ) ) <> 0) \/ ((high_pre % ( 2 ) ) <> 0)) -> ((((high_pre - low_pre ) ÷ 2 ) + 1 ) = (((high_pre - low_pre ) ÷ 2 ) + 1 ))) ”
  &&  emp
.

Definition count_odds_interval_return_wit_2 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ ((high_pre % ( 2 ) ) <> 0) ” 
  &&  “ ((low_pre % ( 2 ) ) = 0) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  emp
|--
  “ ((((low_pre % ( 2 ) ) = 0) /\ ((high_pre % ( 2 ) ) = 0)) -> ((((high_pre - low_pre ) ÷ 2 ) + 1 ) = ((high_pre - low_pre ) ÷ 2 ))) ” 
  &&  “ ((((low_pre % ( 2 ) ) <> 0) \/ ((high_pre % ( 2 ) ) <> 0)) -> ((((high_pre - low_pre ) ÷ 2 ) + 1 ) = (((high_pre - low_pre ) ÷ 2 ) + 1 ))) ”
  &&  emp
.

Definition count_odds_interval_return_wit_3 := 
forall (high_pre: Z) (low_pre: Z) ,
  “ ((high_pre % ( 2 ) ) = 0) ” 
  &&  “ ((low_pre % ( 2 ) ) = 0) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ”
  &&  emp
|--
  “ ((((low_pre % ( 2 ) ) = 0) /\ ((high_pre % ( 2 ) ) = 0)) -> (((high_pre - low_pre ) ÷ 2 ) = ((high_pre - low_pre ) ÷ 2 ))) ” 
  &&  “ ((((low_pre % ( 2 ) ) <> 0) \/ ((high_pre % ( 2 ) ) <> 0)) -> (((high_pre - low_pre ) ÷ 2 ) = (((high_pre - low_pre ) ÷ 2 ) + 1 ))) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_count_odds_interval_safety_wit_1 : count_odds_interval_safety_wit_1.
Axiom proof_of_count_odds_interval_safety_wit_2 : count_odds_interval_safety_wit_2.
Axiom proof_of_count_odds_interval_safety_wit_3 : count_odds_interval_safety_wit_3.
Axiom proof_of_count_odds_interval_safety_wit_4 : count_odds_interval_safety_wit_4.
Axiom proof_of_count_odds_interval_safety_wit_5 : count_odds_interval_safety_wit_5.
Axiom proof_of_count_odds_interval_safety_wit_6 : count_odds_interval_safety_wit_6.
Axiom proof_of_count_odds_interval_safety_wit_7 : count_odds_interval_safety_wit_7.
Axiom proof_of_count_odds_interval_safety_wit_8 : count_odds_interval_safety_wit_8.
Axiom proof_of_count_odds_interval_safety_wit_9 : count_odds_interval_safety_wit_9.
Axiom proof_of_count_odds_interval_safety_wit_10 : count_odds_interval_safety_wit_10.
Axiom proof_of_count_odds_interval_safety_wit_11 : count_odds_interval_safety_wit_11.
Axiom proof_of_count_odds_interval_safety_wit_12 : count_odds_interval_safety_wit_12.
Axiom proof_of_count_odds_interval_safety_wit_13 : count_odds_interval_safety_wit_13.
Axiom proof_of_count_odds_interval_safety_wit_14 : count_odds_interval_safety_wit_14.
Axiom proof_of_count_odds_interval_safety_wit_15 : count_odds_interval_safety_wit_15.
Axiom proof_of_count_odds_interval_safety_wit_16 : count_odds_interval_safety_wit_16.
Axiom proof_of_count_odds_interval_safety_wit_17 : count_odds_interval_safety_wit_17.
Axiom proof_of_count_odds_interval_safety_wit_18 : count_odds_interval_safety_wit_18.
Axiom proof_of_count_odds_interval_safety_wit_19 : count_odds_interval_safety_wit_19.
Axiom proof_of_count_odds_interval_return_wit_1 : count_odds_interval_return_wit_1.
Axiom proof_of_count_odds_interval_return_wit_2 : count_odds_interval_return_wit_2.
Axiom proof_of_count_odds_interval_return_wit_3 : count_odds_interval_return_wit_3.

End VC_Correct.

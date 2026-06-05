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

(*----- Function leap_year -----*)

Definition leap_year_safety_wit_1 := 
forall (year_pre: Z) ,
  “ (1 <= year_pre) ”
  &&  ((( &( "year" ) )) # Int  |-> year_pre)
|--
  “ ((year_pre <> (INT_MIN)) \/ (400 <> (-1))) ” 
  &&  “ (400 <> 0) ”
.

Definition leap_year_safety_wit_2 := 
forall (year_pre: Z) ,
  “ (1 <= year_pre) ”
  &&  ((( &( "year" ) )) # Int  |-> year_pre)
|--
  “ (400 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 400) ”
.

Definition leap_year_safety_wit_3 := 
forall (year_pre: Z) ,
  “ (1 <= year_pre) ”
  &&  ((( &( "year" ) )) # Int  |-> year_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition leap_year_safety_wit_4 := 
forall (year_pre: Z) ,
  “ ((year_pre % ( 400 ) ) = 0) ” 
  &&  “ (1 <= year_pre) ”
  &&  ((( &( "year" ) )) # Int  |-> year_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition leap_year_safety_wit_5 := 
forall (year_pre: Z) ,
  “ ((year_pre % ( 400 ) ) <> 0) ” 
  &&  “ (1 <= year_pre) ”
  &&  ((( &( "year" ) )) # Int  |-> year_pre)
|--
  “ ((year_pre <> (INT_MIN)) \/ (100 <> (-1))) ” 
  &&  “ (100 <> 0) ”
.

Definition leap_year_safety_wit_6 := 
forall (year_pre: Z) ,
  “ ((year_pre % ( 400 ) ) <> 0) ” 
  &&  “ (1 <= year_pre) ”
  &&  ((( &( "year" ) )) # Int  |-> year_pre)
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition leap_year_safety_wit_7 := 
forall (year_pre: Z) ,
  “ ((year_pre % ( 400 ) ) <> 0) ” 
  &&  “ (1 <= year_pre) ”
  &&  ((( &( "year" ) )) # Int  |-> year_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition leap_year_safety_wit_8 := 
forall (year_pre: Z) ,
  “ ((year_pre % ( 100 ) ) = 0) ” 
  &&  “ ((year_pre % ( 400 ) ) <> 0) ” 
  &&  “ (1 <= year_pre) ”
  &&  ((( &( "year" ) )) # Int  |-> year_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition leap_year_safety_wit_9 := 
forall (year_pre: Z) ,
  “ ((year_pre % ( 100 ) ) <> 0) ” 
  &&  “ ((year_pre % ( 400 ) ) <> 0) ” 
  &&  “ (1 <= year_pre) ”
  &&  ((( &( "year" ) )) # Int  |-> year_pre)
|--
  “ ((year_pre <> (INT_MIN)) \/ (4 <> (-1))) ” 
  &&  “ (4 <> 0) ”
.

Definition leap_year_safety_wit_10 := 
forall (year_pre: Z) ,
  “ ((year_pre % ( 100 ) ) <> 0) ” 
  &&  “ ((year_pre % ( 400 ) ) <> 0) ” 
  &&  “ (1 <= year_pre) ”
  &&  ((( &( "year" ) )) # Int  |-> year_pre)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition leap_year_safety_wit_11 := 
forall (year_pre: Z) ,
  “ ((year_pre % ( 100 ) ) <> 0) ” 
  &&  “ ((year_pre % ( 400 ) ) <> 0) ” 
  &&  “ (1 <= year_pre) ”
  &&  ((( &( "year" ) )) # Int  |-> year_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition leap_year_return_wit_1 := 
forall (year_pre: Z) ,
  “ ((year_pre % ( 4 ) ) = 0) ” 
  &&  “ ((year_pre % ( 100 ) ) <> 0) ” 
  &&  “ ((year_pre % ( 400 ) ) <> 0) ” 
  &&  “ (1 <= year_pre) ”
  &&  emp
|--
  “ (((year_pre % ( 400 ) ) = 0) -> (1 = 1)) ” 
  &&  “ ((((year_pre % ( 100 ) ) = 0) /\ ((year_pre % ( 400 ) ) <> 0)) -> (1 = 0)) ” 
  &&  “ ((((year_pre % ( 4 ) ) = 0) /\ ((year_pre % ( 100 ) ) <> 0)) -> (1 = 1)) ” 
  &&  “ (((year_pre % ( 4 ) ) <> 0) -> (1 = 0)) ”
  &&  emp
.

Definition leap_year_return_wit_2 := 
forall (year_pre: Z) ,
  “ ((year_pre % ( 4 ) ) <> 0) ” 
  &&  “ ((year_pre % ( 100 ) ) <> 0) ” 
  &&  “ ((year_pre % ( 400 ) ) <> 0) ” 
  &&  “ (1 <= year_pre) ”
  &&  emp
|--
  “ (((year_pre % ( 400 ) ) = 0) -> (0 = 1)) ” 
  &&  “ ((((year_pre % ( 100 ) ) = 0) /\ ((year_pre % ( 400 ) ) <> 0)) -> (0 = 0)) ” 
  &&  “ ((((year_pre % ( 4 ) ) = 0) /\ ((year_pre % ( 100 ) ) <> 0)) -> (0 = 1)) ” 
  &&  “ (((year_pre % ( 4 ) ) <> 0) -> (0 = 0)) ”
  &&  emp
.

Definition leap_year_return_wit_3 := 
forall (year_pre: Z) ,
  “ ((year_pre % ( 100 ) ) = 0) ” 
  &&  “ ((year_pre % ( 400 ) ) <> 0) ” 
  &&  “ (1 <= year_pre) ”
  &&  emp
|--
  “ (((year_pre % ( 400 ) ) = 0) -> (0 = 1)) ” 
  &&  “ ((((year_pre % ( 100 ) ) = 0) /\ ((year_pre % ( 400 ) ) <> 0)) -> (0 = 0)) ” 
  &&  “ ((((year_pre % ( 4 ) ) = 0) /\ ((year_pre % ( 100 ) ) <> 0)) -> (0 = 1)) ” 
  &&  “ (((year_pre % ( 4 ) ) <> 0) -> (0 = 0)) ”
  &&  emp
.

Definition leap_year_return_wit_4 := 
forall (year_pre: Z) ,
  “ ((year_pre % ( 400 ) ) = 0) ” 
  &&  “ (1 <= year_pre) ”
  &&  emp
|--
  “ (((year_pre % ( 400 ) ) = 0) -> (1 = 1)) ” 
  &&  “ ((((year_pre % ( 100 ) ) = 0) /\ ((year_pre % ( 400 ) ) <> 0)) -> (1 = 0)) ” 
  &&  “ ((((year_pre % ( 4 ) ) = 0) /\ ((year_pre % ( 100 ) ) <> 0)) -> (1 = 1)) ” 
  &&  “ (((year_pre % ( 4 ) ) <> 0) -> (1 = 0)) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_leap_year_safety_wit_1 : leap_year_safety_wit_1.
Axiom proof_of_leap_year_safety_wit_2 : leap_year_safety_wit_2.
Axiom proof_of_leap_year_safety_wit_3 : leap_year_safety_wit_3.
Axiom proof_of_leap_year_safety_wit_4 : leap_year_safety_wit_4.
Axiom proof_of_leap_year_safety_wit_5 : leap_year_safety_wit_5.
Axiom proof_of_leap_year_safety_wit_6 : leap_year_safety_wit_6.
Axiom proof_of_leap_year_safety_wit_7 : leap_year_safety_wit_7.
Axiom proof_of_leap_year_safety_wit_8 : leap_year_safety_wit_8.
Axiom proof_of_leap_year_safety_wit_9 : leap_year_safety_wit_9.
Axiom proof_of_leap_year_safety_wit_10 : leap_year_safety_wit_10.
Axiom proof_of_leap_year_safety_wit_11 : leap_year_safety_wit_11.
Axiom proof_of_leap_year_return_wit_1 : leap_year_return_wit_1.
Axiom proof_of_leap_year_return_wit_2 : leap_year_return_wit_2.
Axiom proof_of_leap_year_return_wit_3 : leap_year_return_wit_3.
Axiom proof_of_leap_year_return_wit_4 : leap_year_return_wit_4.

End VC_Correct.

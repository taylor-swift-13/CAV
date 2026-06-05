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

(*----- Function ex_difference_of_squares -----*)

Definition ex_difference_of_squares_safety_wit_1 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((2 * n_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) )) ” 
  &&  “ (((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) ) <= INT_MAX) ”
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (((n_pre * (n_pre + 1 ) ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition ex_difference_of_squares_safety_wit_2 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((2 * n_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) )) ” 
  &&  “ (((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) ) <= INT_MAX) ”
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre * (n_pre + 1 ) )) ”
.

Definition ex_difference_of_squares_safety_wit_3 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((2 * n_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) )) ” 
  &&  “ (((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) ) <= INT_MAX) ”
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition ex_difference_of_squares_safety_wit_4 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((2 * n_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) )) ” 
  &&  “ (((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) ) <= INT_MAX) ”
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ex_difference_of_squares_safety_wit_5 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((2 * n_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) )) ” 
  &&  “ (((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) ) <= INT_MAX) ”
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition ex_difference_of_squares_safety_wit_6 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((2 * n_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) )) ” 
  &&  “ (((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) ) <= INT_MAX) ”
  &&  ((( &( "square_sum" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> ((n_pre * (n_pre + 1 ) ) ÷ 2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) <> (INT_MIN)) \/ (6 <> (-1))) ” 
  &&  “ (6 <> 0) ”
.

Definition ex_difference_of_squares_safety_wit_7 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((2 * n_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) )) ” 
  &&  “ (((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) ) <= INT_MAX) ”
  &&  ((( &( "square_sum" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> ((n_pre * (n_pre + 1 ) ) ÷ 2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) )) ”
.

Definition ex_difference_of_squares_safety_wit_8 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((2 * n_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) )) ” 
  &&  “ (((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) ) <= INT_MAX) ”
  &&  ((( &( "square_sum" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> ((n_pre * (n_pre + 1 ) ) ÷ 2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (((2 * n_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * n_pre ) + 1 )) ”
.

Definition ex_difference_of_squares_safety_wit_9 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((2 * n_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) )) ” 
  &&  “ (((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) ) <= INT_MAX) ”
  &&  ((( &( "square_sum" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> ((n_pre * (n_pre + 1 ) ) ÷ 2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((2 * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * n_pre )) ”
.

Definition ex_difference_of_squares_safety_wit_10 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((2 * n_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) )) ” 
  &&  “ (((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) ) <= INT_MAX) ”
  &&  ((( &( "square_sum" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> ((n_pre * (n_pre + 1 ) ) ÷ 2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre * (n_pre + 1 ) )) ”
.

Definition ex_difference_of_squares_safety_wit_11 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((2 * n_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) )) ” 
  &&  “ (((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) ) <= INT_MAX) ”
  &&  ((( &( "square_sum" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> ((n_pre * (n_pre + 1 ) ) ÷ 2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition ex_difference_of_squares_safety_wit_12 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((2 * n_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) )) ” 
  &&  “ (((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) ) <= INT_MAX) ”
  &&  ((( &( "square_sum" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> ((n_pre * (n_pre + 1 ) ) ÷ 2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ex_difference_of_squares_safety_wit_13 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((2 * n_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) )) ” 
  &&  “ (((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) ) <= INT_MAX) ”
  &&  ((( &( "square_sum" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> ((n_pre * (n_pre + 1 ) ) ÷ 2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition ex_difference_of_squares_safety_wit_14 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((2 * n_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) )) ” 
  &&  “ (((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) ) <= INT_MAX) ”
  &&  ((( &( "square_sum" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> ((n_pre * (n_pre + 1 ) ) ÷ 2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ex_difference_of_squares_safety_wit_15 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((2 * n_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) )) ” 
  &&  “ (((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) ) <= INT_MAX) ”
  &&  ((( &( "square_sum" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> ((n_pre * (n_pre + 1 ) ) ÷ 2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (6 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 6) ”
.

Definition ex_difference_of_squares_safety_wit_16 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((2 * n_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) )) ” 
  &&  “ (((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) ) <= INT_MAX) ”
  &&  ((( &( "square_sum" ) )) # Int  |-> (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ))
  **  ((( &( "sum" ) )) # Int  |-> ((n_pre * (n_pre + 1 ) ) ÷ 2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) )) ”
.

Definition ex_difference_of_squares_safety_wit_17 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((2 * n_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) )) ” 
  &&  “ (((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) ) <= INT_MAX) ”
  &&  ((( &( "square_sum" ) )) # Int  |-> (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ))
  **  ((( &( "sum" ) )) # Int  |-> ((n_pre * (n_pre + 1 ) ) ÷ 2 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) )) ”
.

Definition ex_difference_of_squares_return_wit_1 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((2 * n_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) )) ” 
  &&  “ (((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) ) <= INT_MAX) ”
  &&  emp
|--
  “ (((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) ) = ((((n_pre * (n_pre + 1 ) ) ÷ 2 ) * ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) - (((n_pre * (n_pre + 1 ) ) * ((2 * n_pre ) + 1 ) ) ÷ 6 ) )) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_ex_difference_of_squares_safety_wit_1 : ex_difference_of_squares_safety_wit_1.
Axiom proof_of_ex_difference_of_squares_safety_wit_2 : ex_difference_of_squares_safety_wit_2.
Axiom proof_of_ex_difference_of_squares_safety_wit_3 : ex_difference_of_squares_safety_wit_3.
Axiom proof_of_ex_difference_of_squares_safety_wit_4 : ex_difference_of_squares_safety_wit_4.
Axiom proof_of_ex_difference_of_squares_safety_wit_5 : ex_difference_of_squares_safety_wit_5.
Axiom proof_of_ex_difference_of_squares_safety_wit_6 : ex_difference_of_squares_safety_wit_6.
Axiom proof_of_ex_difference_of_squares_safety_wit_7 : ex_difference_of_squares_safety_wit_7.
Axiom proof_of_ex_difference_of_squares_safety_wit_8 : ex_difference_of_squares_safety_wit_8.
Axiom proof_of_ex_difference_of_squares_safety_wit_9 : ex_difference_of_squares_safety_wit_9.
Axiom proof_of_ex_difference_of_squares_safety_wit_10 : ex_difference_of_squares_safety_wit_10.
Axiom proof_of_ex_difference_of_squares_safety_wit_11 : ex_difference_of_squares_safety_wit_11.
Axiom proof_of_ex_difference_of_squares_safety_wit_12 : ex_difference_of_squares_safety_wit_12.
Axiom proof_of_ex_difference_of_squares_safety_wit_13 : ex_difference_of_squares_safety_wit_13.
Axiom proof_of_ex_difference_of_squares_safety_wit_14 : ex_difference_of_squares_safety_wit_14.
Axiom proof_of_ex_difference_of_squares_safety_wit_15 : ex_difference_of_squares_safety_wit_15.
Axiom proof_of_ex_difference_of_squares_safety_wit_16 : ex_difference_of_squares_safety_wit_16.
Axiom proof_of_ex_difference_of_squares_safety_wit_17 : ex_difference_of_squares_safety_wit_17.
Axiom proof_of_ex_difference_of_squares_return_wit_1 : ex_difference_of_squares_return_wit_1.

End VC_Correct.

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
Require Import p131_digits.
Local Open Scope sac.

(*----- Function p131_digits -----*)

Definition p131_digits_safety_wit_1 := 
forall (n_pre: Z) ,
  “ (problem_131_pre n_pre ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n_pre)) <= INT_MAX) ”
  &&  ((( &( "has" ) )) # Int  |->_)
  **  ((( &( "prod" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p131_digits_safety_wit_2 := 
forall (n_pre: Z) ,
  “ (problem_131_pre n_pre ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n_pre)) <= INT_MAX) ”
  &&  ((( &( "prod" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p131_digits_safety_wit_3 := 
forall (n_pre: Z) ,
  “ (problem_131_pre n_pre ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n_pre)) <= INT_MAX) ”
  &&  ((( &( "has" ) )) # Int  |-> 0)
  **  ((( &( "prod" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p131_digits_safety_wit_4 := 
forall (n_pre: Z) ,
  “ (n_pre = 0) ” 
  &&  “ (problem_131_pre n_pre ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n_pre)) <= INT_MAX) ”
  &&  ((( &( "has" ) )) # Int  |-> 0)
  **  ((( &( "prod" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ False ”
.

Definition p131_digits_safety_wit_5 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 1) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p131_digits_safety_wit_6 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 0) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p131_digits_safety_wit_7 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 0) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ ((n <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition p131_digits_safety_wit_8 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 0) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition p131_digits_safety_wit_9 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 1) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ ((n <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition p131_digits_safety_wit_10 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 1) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition p131_digits_safety_wit_11 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 0) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ (((n % ( 10 ) ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition p131_digits_safety_wit_12 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 1) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ (((n % ( 10 ) ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition p131_digits_safety_wit_13 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 1) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p131_digits_safety_wit_14 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 0) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p131_digits_safety_wit_15 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 1) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p131_digits_safety_wit_16 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 0) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p131_digits_safety_wit_17 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 0) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p131_digits_safety_wit_18 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 1) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p131_digits_safety_wit_19 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 1) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> 1)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ ((prod * (n % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (prod * (n % ( 10 ) ) )) ”
.

Definition p131_digits_safety_wit_20 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 0) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> 1)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ ((prod * (n % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (prod * (n % ( 10 ) ) )) ”
.

Definition p131_digits_safety_wit_21 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) <> 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 0) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ ((n <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition p131_digits_safety_wit_22 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) <> 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 0) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition p131_digits_safety_wit_23 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) <> 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 1) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ ((n <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition p131_digits_safety_wit_24 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) <> 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 1) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition p131_digits_safety_wit_25 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 0) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> 1)
  **  ((( &( "prod" ) )) # Int  |-> (prod * (n % ( 10 ) ) ))
|--
  “ ((n <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition p131_digits_safety_wit_26 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 0) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> 1)
  **  ((( &( "prod" ) )) # Int  |-> (prod * (n % ( 10 ) ) ))
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition p131_digits_safety_wit_27 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 1) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> 1)
  **  ((( &( "prod" ) )) # Int  |-> (prod * (n % ( 10 ) ) ))
|--
  “ ((n <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition p131_digits_safety_wit_28 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 1) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> 1)
  **  ((( &( "prod" ) )) # Int  |-> (prod * (n % ( 10 ) ) ))
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition p131_digits_safety_wit_29 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (n <= 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 0) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p131_digits_safety_wit_30 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (n <= 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 1) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p131_digits_safety_wit_31 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (has <> 0) ” 
  &&  “ (n <= 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 0) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ False ”
.

Definition p131_digits_safety_wit_32 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (has = 0) ” 
  &&  “ (n <= 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 1) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ False ”
.

Definition p131_digits_safety_wit_33 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (has = 0) ” 
  &&  “ (n <= 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 0) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p131_digits_entail_wit_1 := 
forall (n_pre: Z) ,
  “ (n_pre <> 0) ” 
  &&  “ (problem_131_pre n_pre ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n_pre)) <= INT_MAX) ”
  &&  emp
|--
  (EX (n0: Z) ,
  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n0) ” 
  &&  “ (0 = 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n_pre) (1) (0))) ” 
  &&  “ ((digits_state (n_pre) (1) (0)) <= INT_MAX) ”
  &&  emp)
  ||
  (EX (n0: Z) ,
  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n_pre) (1) (0))) ” 
  &&  “ ((digits_state (n_pre) (1) (0)) <= INT_MAX) ”
  &&  emp)
.

Definition p131_digits_entail_wit_2_1 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0_2: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (n0_2 = n_pre) ” 
  &&  “ (1 <= n0_2) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0_2) ” 
  &&  “ (has = 1) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0_2)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  emp
|--
  (EX (n0: Z) ,
  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n0) ” 
  &&  “ (1 = 1) ” 
  &&  “ (1 <= (prod * (n % ( 10 ) ) )) ” 
  &&  “ ((prod * (n % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state ((n ÷ 10 )) ((prod * (n % ( 10 ) ) )) (1))) ” 
  &&  “ ((digits_state ((n ÷ 10 )) ((prod * (n % ( 10 ) ) )) (1)) <= INT_MAX) ”
  &&  emp)
  ||
  (EX (n0: Z) ,
  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n0) ” 
  &&  “ (1 = 0) ” 
  &&  “ (1 <= (prod * (n % ( 10 ) ) )) ” 
  &&  “ ((prod * (n % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state ((n ÷ 10 )) ((prod * (n % ( 10 ) ) )) (1))) ” 
  &&  “ ((digits_state ((n ÷ 10 )) ((prod * (n % ( 10 ) ) )) (1)) <= INT_MAX) ”
  &&  emp)
.

Definition p131_digits_entail_wit_2_2 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0_2: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (n0_2 = n_pre) ” 
  &&  “ (1 <= n0_2) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0_2) ” 
  &&  “ (has = 0) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0_2)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  emp
|--
  (EX (n0: Z) ,
  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n0) ” 
  &&  “ (1 = 1) ” 
  &&  “ (1 <= (prod * (n % ( 10 ) ) )) ” 
  &&  “ ((prod * (n % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state ((n ÷ 10 )) ((prod * (n % ( 10 ) ) )) (1))) ” 
  &&  “ ((digits_state ((n ÷ 10 )) ((prod * (n % ( 10 ) ) )) (1)) <= INT_MAX) ”
  &&  emp)
  ||
  (EX (n0: Z) ,
  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n0) ” 
  &&  “ (1 = 0) ” 
  &&  “ (1 <= (prod * (n % ( 10 ) ) )) ” 
  &&  “ ((prod * (n % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state ((n ÷ 10 )) ((prod * (n % ( 10 ) ) )) (1))) ” 
  &&  “ ((digits_state ((n ÷ 10 )) ((prod * (n % ( 10 ) ) )) (1)) <= INT_MAX) ”
  &&  emp)
.

Definition p131_digits_entail_wit_2_3 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0_2: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) <> 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (n0_2 = n_pre) ” 
  &&  “ (1 <= n0_2) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0_2) ” 
  &&  “ (has = 1) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0_2)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  emp
|--
  (EX (n0: Z) ,
  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n0) ” 
  &&  “ (has = 1) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state ((n ÷ 10 )) (prod) (has))) ” 
  &&  “ ((digits_state ((n ÷ 10 )) (prod) (has)) <= INT_MAX) ”
  &&  emp)
  ||
  (EX (n0: Z) ,
  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n0) ” 
  &&  “ (has = 0) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state ((n ÷ 10 )) (prod) (has))) ” 
  &&  “ ((digits_state ((n ÷ 10 )) (prod) (has)) <= INT_MAX) ”
  &&  emp)
.

Definition p131_digits_entail_wit_2_4 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0_2: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) <> 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (n0_2 = n_pre) ” 
  &&  “ (1 <= n0_2) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0_2) ” 
  &&  “ (has = 0) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0_2)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  emp
|--
  (EX (n0: Z) ,
  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n0) ” 
  &&  “ (has = 1) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state ((n ÷ 10 )) (prod) (has))) ” 
  &&  “ ((digits_state ((n ÷ 10 )) (prod) (has)) <= INT_MAX) ”
  &&  emp)
  ||
  (EX (n0: Z) ,
  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n0) ” 
  &&  “ (has = 0) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state ((n ÷ 10 )) (prod) (has))) ” 
  &&  “ ((digits_state ((n ÷ 10 )) (prod) (has)) <= INT_MAX) ”
  &&  emp)
.

Definition p131_digits_return_wit_1 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (has <> 0) ” 
  &&  “ (n <= 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 1) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  emp
|--
  “ (problem_131_spec n_pre prod ) ”
  &&  emp
.

Definition p131_digits_return_wit_2 := 
forall (n_pre: Z) (prod: Z) (has: Z) (n: Z) (n0: Z) ,
  “ (has = 0) ” 
  &&  “ (n <= 0) ” 
  &&  “ (n0 = n_pre) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n0) ” 
  &&  “ (has = 0) ” 
  &&  “ (1 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n0)) = (digits_state (n) (prod) (has))) ” 
  &&  “ ((digits_state (n) (prod) (has)) <= INT_MAX) ”
  &&  emp
|--
  “ (problem_131_spec n_pre 0 ) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_p131_digits_safety_wit_1 : p131_digits_safety_wit_1.
Axiom proof_of_p131_digits_safety_wit_2 : p131_digits_safety_wit_2.
Axiom proof_of_p131_digits_safety_wit_3 : p131_digits_safety_wit_3.
Axiom proof_of_p131_digits_safety_wit_4 : p131_digits_safety_wit_4.
Axiom proof_of_p131_digits_safety_wit_5 : p131_digits_safety_wit_5.
Axiom proof_of_p131_digits_safety_wit_6 : p131_digits_safety_wit_6.
Axiom proof_of_p131_digits_safety_wit_7 : p131_digits_safety_wit_7.
Axiom proof_of_p131_digits_safety_wit_8 : p131_digits_safety_wit_8.
Axiom proof_of_p131_digits_safety_wit_9 : p131_digits_safety_wit_9.
Axiom proof_of_p131_digits_safety_wit_10 : p131_digits_safety_wit_10.
Axiom proof_of_p131_digits_safety_wit_11 : p131_digits_safety_wit_11.
Axiom proof_of_p131_digits_safety_wit_12 : p131_digits_safety_wit_12.
Axiom proof_of_p131_digits_safety_wit_13 : p131_digits_safety_wit_13.
Axiom proof_of_p131_digits_safety_wit_14 : p131_digits_safety_wit_14.
Axiom proof_of_p131_digits_safety_wit_15 : p131_digits_safety_wit_15.
Axiom proof_of_p131_digits_safety_wit_16 : p131_digits_safety_wit_16.
Axiom proof_of_p131_digits_safety_wit_17 : p131_digits_safety_wit_17.
Axiom proof_of_p131_digits_safety_wit_18 : p131_digits_safety_wit_18.
Axiom proof_of_p131_digits_safety_wit_19 : p131_digits_safety_wit_19.
Axiom proof_of_p131_digits_safety_wit_20 : p131_digits_safety_wit_20.
Axiom proof_of_p131_digits_safety_wit_21 : p131_digits_safety_wit_21.
Axiom proof_of_p131_digits_safety_wit_22 : p131_digits_safety_wit_22.
Axiom proof_of_p131_digits_safety_wit_23 : p131_digits_safety_wit_23.
Axiom proof_of_p131_digits_safety_wit_24 : p131_digits_safety_wit_24.
Axiom proof_of_p131_digits_safety_wit_25 : p131_digits_safety_wit_25.
Axiom proof_of_p131_digits_safety_wit_26 : p131_digits_safety_wit_26.
Axiom proof_of_p131_digits_safety_wit_27 : p131_digits_safety_wit_27.
Axiom proof_of_p131_digits_safety_wit_28 : p131_digits_safety_wit_28.
Axiom proof_of_p131_digits_safety_wit_29 : p131_digits_safety_wit_29.
Axiom proof_of_p131_digits_safety_wit_30 : p131_digits_safety_wit_30.
Axiom proof_of_p131_digits_safety_wit_31 : p131_digits_safety_wit_31.
Axiom proof_of_p131_digits_safety_wit_32 : p131_digits_safety_wit_32.
Axiom proof_of_p131_digits_safety_wit_33 : p131_digits_safety_wit_33.
Axiom proof_of_p131_digits_entail_wit_1 : p131_digits_entail_wit_1.
Axiom proof_of_p131_digits_entail_wit_2_1 : p131_digits_entail_wit_2_1.
Axiom proof_of_p131_digits_entail_wit_2_2 : p131_digits_entail_wit_2_2.
Axiom proof_of_p131_digits_entail_wit_2_3 : p131_digits_entail_wit_2_3.
Axiom proof_of_p131_digits_entail_wit_2_4 : p131_digits_entail_wit_2_4.
Axiom proof_of_p131_digits_return_wit_1 : p131_digits_return_wit_1.
Axiom proof_of_p131_digits_return_wit_2 : p131_digits_return_wit_2.

End VC_Correct.
